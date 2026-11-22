import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q4M1L4

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨4, 1, 4⟩

private def box_6 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (85 / 512 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (113 / 512 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_5 : Tree := .splitD (33 / 160 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_9 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_9 : Tree := .leaf (.strip (181 / 1024 : ℚ))
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (235 / 1024 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_8 : Tree := .splitD (33 / 160 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_4 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_4 : Tree := .splitC (33 / 160 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_13 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ), (7 / 32 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (7 / 32 : ℚ), (9 / 40 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_12 : Tree := .splitD (7 / 32 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_16 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (17 / 80 : ℚ), (7 / 32 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (7 / 32 : ℚ), (9 / 40 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_15 : Tree := .splitD (7 / 32 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_11 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_11 : Tree := .splitC (33 / 160 : ℚ) node_12 node_15
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitCValid box_11 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_11], node_12_accepts, node_15_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_3 : Tree := .splitD (17 / 80 : ℚ) node_4 node_11
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_11_accepts⟩

private def box_21 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_21 : Tree := .leaf (.strip (47 / 256 : ℚ))
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_20 : Tree := .splitD (33 / 160 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_24 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_24 : Tree := .leaf (.strip (95 / 512 : ℚ))
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_23 : Tree := .splitD (33 / 160 : ℚ) node_24 node_25
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitDValid box_23 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_23], node_24_accepts, node_25_accepts⟩

private def box_19 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_19 : Tree := .splitC (7 / 32 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitCValid box_19 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_26 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_18 : Tree := .splitD (17 / 80 : ℚ) node_19 node_26
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_26_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_2 : Tree := .splitC (17 / 80 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_28 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_27 : Tree := .splitC (17 / 80 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitCValid box_27 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_1 : Tree := .splitD (9 / 40 : ℚ) node_2 node_27
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_27_accepts⟩

private def box_35 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_34 : Tree := .splitD (33 / 160 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_38 : Rectangle := ⟨(37 / 160 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(37 / 160 : ℚ), (19 / 80 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(37 / 160 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_37 : Tree := .splitD (33 / 160 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_33 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_33 : Tree := .splitC (37 / 160 : ℚ) node_34 node_37
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitCValid box_33 (37 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_33], node_34_accepts, node_37_accepts⟩

private def box_40 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_32 : Tree := .splitD (17 / 80 : ℚ) node_33 node_40
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitDValid box_32 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_32], node_33_accepts, node_40_accepts⟩

private def box_42 : Rectangle := ⟨(19 / 80 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(19 / 80 : ℚ), (1 / 4 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(19 / 80 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_41 : Tree := .splitD (17 / 80 : ℚ) node_42 node_43
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitDValid box_41 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_41], node_42_accepts, node_43_accepts⟩

private def box_31 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_31 : Tree := .splitC (19 / 80 : ℚ) node_32 node_41
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_41_accepts⟩

private def box_44 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_30 : Tree := .splitD (9 / 40 : ℚ) node_31 node_44
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_44_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 5 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_0 : Tree := .splitC (9 / 40 : ℚ) node_1 node_30
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_30_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q4M1L4
