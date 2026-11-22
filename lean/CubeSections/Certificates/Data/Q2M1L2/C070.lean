import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C070

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_7 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_6 : Tree := .splitD (27 / 64 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_10 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_9 : Tree := .splitD (27 / 64 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitDValid box_9 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_5 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_5 : Tree := .splitC (65 / 192 : ℚ) node_6 node_9
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (65 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_9_accepts⟩

private def box_13 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_12 : Tree := .splitC (65 / 192 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (65 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_4 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_4 : Tree := .splitD (41 / 96 : ℚ) node_5 node_12
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_12_accepts⟩

private def box_18 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_17 : Tree := .splitD (27 / 64 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitDValid box_17 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_21 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_20 : Tree := .splitD (27 / 64 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_16 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_16 : Tree := .splitC (67 / 192 : ℚ) node_17 node_20
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitCValid box_16 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_16], node_17_accepts, node_20_accepts⟩

private def box_25 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_24 : Tree := .splitD (83 / 192 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_28 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_27 : Tree := .splitD (83 / 192 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitDValid box_27 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_23 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_23 : Tree := .splitC (67 / 192 : ℚ) node_24 node_27
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitCValid box_23 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_23], node_24_accepts, node_27_accepts⟩

private def box_15 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_15 : Tree := .splitD (41 / 96 : ℚ) node_16 node_23
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_23_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_3 : Tree := .splitC (11 / 32 : ℚ) node_4 node_15
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_15_accepts⟩

private def box_32 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_31 : Tree := .splitD (43 / 96 : ℚ) node_32 node_33
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitDValid box_31 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_31], node_32_accepts, node_33_accepts⟩

private def box_35 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_34 : Tree := .splitD (43 / 96 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_30 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_30 : Tree := .splitC (11 / 32 : ℚ) node_31 node_34
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitCValid box_30 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_30], node_31_accepts, node_34_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_2 : Tree := .splitD (7 / 16 : ℚ) node_3 node_30
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_30_accepts⟩

private def box_43 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_42 : Tree := .splitC (137 / 384 : ℚ) node_43 node_44
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitCValid box_42 (137 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_42], node_43_accepts, node_44_accepts⟩

private def box_45 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_41 : Tree := .splitD (27 / 64 : ℚ) node_42 node_45
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitDValid box_41 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_41], node_42_accepts, node_45_accepts⟩

private def box_48 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_51 : Tree := .leaf .projection
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_49 : Tree := .splitD (161 / 384 : ℚ) node_50 node_51
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitDValid box_49 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_49], node_50_accepts, node_51_accepts⟩

private def box_47 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_47 : Tree := .splitC (139 / 384 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitCValid box_47 (139 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_53 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_53 : Tree := .leaf .projection
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_52 : Tree := .splitC (139 / 384 : ℚ) node_53 node_54
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitCValid box_52 (139 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_52], node_53_accepts, node_54_accepts⟩

private def box_46 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_46 : Tree := .splitD (27 / 64 : ℚ) node_47 node_52
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitDValid box_46 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_46], node_47_accepts, node_52_accepts⟩

private def box_40 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_40 : Tree := .splitC (23 / 64 : ℚ) node_41 node_46
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitCValid box_40 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_40], node_41_accepts, node_46_accepts⟩

private def box_57 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_56 : Tree := .splitD (83 / 192 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitDValid box_56 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_60 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_60 : Tree := .leaf .projection
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_59 : Tree := .splitD (83 / 192 : ℚ) node_60 node_61
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitDValid box_59 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_59], node_60_accepts, node_61_accepts⟩

private def box_55 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_55 : Tree := .splitC (23 / 64 : ℚ) node_56 node_59
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitCValid box_55 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_55], node_56_accepts, node_59_accepts⟩

private def box_39 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_39 : Tree := .splitD (41 / 96 : ℚ) node_40 node_55
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitDValid box_39 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_39], node_40_accepts, node_55_accepts⟩

private def box_67 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_67 : Tree := .leaf .projection
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_68 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_66 : Tree := .splitD (161 / 384 : ℚ) node_67 node_68
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitDValid box_66 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_66], node_67_accepts, node_68_accepts⟩

private def box_70 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_70 : Tree := .leaf .projection
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  norm_num [Tree.Accepts, node_70, box_70, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_69 : Tree := .splitD (161 / 384 : ℚ) node_70 node_71
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  change SplitDValid box_69 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_69], node_70_accepts, node_71_accepts⟩

private def box_65 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_65 : Tree := .splitC (47 / 128 : ℚ) node_66 node_69
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitCValid box_65 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_65], node_66_accepts, node_69_accepts⟩

private def box_73 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_73 : Tree := .leaf .projection
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  norm_num [Tree.Accepts, node_73, box_73, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_74 : Tree := .leaf .projection
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  norm_num [Tree.Accepts, node_74, box_74, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_72 : Tree := .splitC (47 / 128 : ℚ) node_73 node_74
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitCValid box_72 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_72], node_73_accepts, node_74_accepts⟩

private def box_64 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_64 : Tree := .splitD (27 / 64 : ℚ) node_65 node_72
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitDValid box_64 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_64], node_65_accepts, node_72_accepts⟩

private def box_78 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_78 : Tree := .leaf .projection
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_79 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_79 : Tree := .leaf .projection
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_77 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_77 : Tree := .splitD (161 / 384 : ℚ) node_78 node_79
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitDValid box_77 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_77], node_78_accepts, node_79_accepts⟩

private def box_81 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_81 : Tree := .leaf .projection
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  norm_num [Tree.Accepts, node_81, box_81, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_82 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_82 : Tree := .leaf .projection
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_80 : Tree := .splitD (161 / 384 : ℚ) node_81 node_82
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitDValid box_80 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_80], node_81_accepts, node_82_accepts⟩

private def box_76 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_76 : Tree := .splitC (143 / 384 : ℚ) node_77 node_80
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  change SplitCValid box_76 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_76], node_77_accepts, node_80_accepts⟩

private def box_84 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_84 : Tree := .leaf .projection
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  norm_num [Tree.Accepts, node_84, box_84, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_85 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_85 : Tree := .leaf .projection
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  norm_num [Tree.Accepts, node_85, box_85, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_83 : Tree := .splitC (143 / 384 : ℚ) node_84 node_85
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  change SplitCValid box_83 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_83], node_84_accepts, node_85_accepts⟩

private def box_75 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_75 : Tree := .splitD (27 / 64 : ℚ) node_76 node_83
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  change SplitDValid box_75 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_75], node_76_accepts, node_83_accepts⟩

private def box_63 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_63 : Tree := .splitC (71 / 192 : ℚ) node_64 node_75
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitCValid box_63 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_63], node_64_accepts, node_75_accepts⟩

private def box_88 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_88 : Tree := .leaf .projection
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  norm_num [Tree.Accepts, node_88, box_88, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_89 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_89 : Tree := .leaf .projection
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_87 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_87 : Tree := .splitD (83 / 192 : ℚ) node_88 node_89
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  change SplitDValid box_87 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_87], node_88_accepts, node_89_accepts⟩

private def box_91 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_91 : Tree := .leaf .projection
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  norm_num [Tree.Accepts, node_91, box_91, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_92 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_92 : Tree := .leaf .projection
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  norm_num [Tree.Accepts, node_92, box_92, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_90 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_90 : Tree := .splitD (83 / 192 : ℚ) node_91 node_92
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  change SplitDValid box_90 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_90], node_91_accepts, node_92_accepts⟩

private def box_86 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_86 : Tree := .splitC (71 / 192 : ℚ) node_87 node_90
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  change SplitCValid box_86 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_86], node_87_accepts, node_90_accepts⟩

private def box_62 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_62 : Tree := .splitD (41 / 96 : ℚ) node_63 node_86
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitDValid box_62 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_62], node_63_accepts, node_86_accepts⟩

private def box_38 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_38 : Tree := .splitC (35 / 96 : ℚ) node_39 node_62
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitCValid box_38 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_38], node_39_accepts, node_62_accepts⟩

private def box_96 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_96 : Tree := .leaf .projection
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  norm_num [Tree.Accepts, node_96, box_96, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_98 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (7 / 16 : ℚ), (85 / 192 : ℚ)⟩
private def node_98 : Tree := .leaf .projection
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  norm_num [Tree.Accepts, node_98, box_98, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_99 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (85 / 192 : ℚ), (43 / 96 : ℚ)⟩
private def node_99 : Tree := .leaf .projection
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  norm_num [Tree.Accepts, node_99, box_99, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_97 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_97 : Tree := .splitD (85 / 192 : ℚ) node_98 node_99
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  change SplitDValid box_97 (85 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_97], node_98_accepts, node_99_accepts⟩

private def box_95 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_95 : Tree := .splitC (23 / 64 : ℚ) node_96 node_97
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  change SplitCValid box_95 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_95], node_96_accepts, node_97_accepts⟩

private def box_100 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_100 : Tree := .leaf .projection
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  norm_num [Tree.Accepts, node_100, box_100, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_94 : Tree := .splitD (43 / 96 : ℚ) node_95 node_100
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  change SplitDValid box_94 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_94], node_95_accepts, node_100_accepts⟩

private def box_104 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (7 / 16 : ℚ), (85 / 192 : ℚ)⟩
private def node_104 : Tree := .leaf .projection
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  norm_num [Tree.Accepts, node_104, box_104, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_105 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (85 / 192 : ℚ), (43 / 96 : ℚ)⟩
private def node_105 : Tree := .leaf .projection
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  norm_num [Tree.Accepts, node_105, box_105, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_103 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_103 : Tree := .splitD (85 / 192 : ℚ) node_104 node_105
private theorem node_103_accepts : node_103.Accepts parameters box_103 := by
  change SplitDValid box_103 (85 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_103], node_104_accepts, node_105_accepts⟩

private def box_107 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (85 / 192 : ℚ)⟩
private def node_107 : Tree := .leaf .projection
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  norm_num [Tree.Accepts, node_107, box_107, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_108 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (85 / 192 : ℚ), (43 / 96 : ℚ)⟩
private def node_108 : Tree := .leaf .projection
private theorem node_108_accepts : node_108.Accepts parameters box_108 := by
  norm_num [Tree.Accepts, node_108, box_108, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_106 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_106 : Tree := .splitD (85 / 192 : ℚ) node_107 node_108
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  change SplitDValid box_106 (85 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_106], node_107_accepts, node_108_accepts⟩

private def box_102 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_102 : Tree := .splitC (71 / 192 : ℚ) node_103 node_106
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  change SplitCValid box_102 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_102], node_103_accepts, node_106_accepts⟩

private def box_110 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_110 : Tree := .leaf .projection
private theorem node_110_accepts : node_110.Accepts parameters box_110 := by
  norm_num [Tree.Accepts, node_110, box_110, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_111 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_111 : Tree := .leaf .projection
private theorem node_111_accepts : node_111.Accepts parameters box_111 := by
  norm_num [Tree.Accepts, node_111, box_111, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_109 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_109 : Tree := .splitC (71 / 192 : ℚ) node_110 node_111
private theorem node_109_accepts : node_109.Accepts parameters box_109 := by
  change SplitCValid box_109 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_109], node_110_accepts, node_111_accepts⟩

private def box_101 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_101 : Tree := .splitD (43 / 96 : ℚ) node_102 node_109
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  change SplitDValid box_101 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_101], node_102_accepts, node_109_accepts⟩

private def box_93 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_93 : Tree := .splitC (35 / 96 : ℚ) node_94 node_101
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  change SplitCValid box_93 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_93], node_94_accepts, node_101_accepts⟩

private def box_37 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_37 : Tree := .splitD (7 / 16 : ℚ) node_38 node_93
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_93_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_1 : Tree := .splitC (17 / 48 : ℚ) node_2 node_37
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_37_accepts⟩

private def box_115 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_115 : Tree := .leaf .projection
private theorem node_115_accepts : node_115.Accepts parameters box_115 := by
  norm_num [Tree.Accepts, node_115, box_115, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_116 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_116 : Tree := .leaf .projection
private theorem node_116_accepts : node_116.Accepts parameters box_116 := by
  norm_num [Tree.Accepts, node_116, box_116, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_114 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_114 : Tree := .splitC (11 / 32 : ℚ) node_115 node_116
private theorem node_114_accepts : node_114.Accepts parameters box_114 := by
  change SplitCValid box_114 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_114], node_115_accepts, node_116_accepts⟩

private def box_117 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (23 / 48 : ℚ), (1 / 2 : ℚ)⟩
private def node_117 : Tree := .leaf .projection
private theorem node_117_accepts : node_117.Accepts parameters box_117 := by
  norm_num [Tree.Accepts, node_117, box_117, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_113 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_113 : Tree := .splitD (23 / 48 : ℚ) node_114 node_117
private theorem node_113_accepts : node_113.Accepts parameters box_113 := by
  change SplitDValid box_113 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_113], node_114_accepts, node_117_accepts⟩

private def box_121 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (11 / 24 : ℚ), (15 / 32 : ℚ)⟩
private def node_121 : Tree := .leaf .projection
private theorem node_121_accepts : node_121.Accepts parameters box_121 := by
  norm_num [Tree.Accepts, node_121, box_121, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_122 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (15 / 32 : ℚ), (23 / 48 : ℚ)⟩
private def node_122 : Tree := .leaf .projection
private theorem node_122_accepts : node_122.Accepts parameters box_122 := by
  norm_num [Tree.Accepts, node_122, box_122, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_120 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_120 : Tree := .splitD (15 / 32 : ℚ) node_121 node_122
private theorem node_120_accepts : node_120.Accepts parameters box_120 := by
  change SplitDValid box_120 (15 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_120], node_121_accepts, node_122_accepts⟩

private def box_124 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (11 / 24 : ℚ), (15 / 32 : ℚ)⟩
private def node_124 : Tree := .leaf .projection
private theorem node_124_accepts : node_124.Accepts parameters box_124 := by
  norm_num [Tree.Accepts, node_124, box_124, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_125 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (15 / 32 : ℚ), (23 / 48 : ℚ)⟩
private def node_125 : Tree := .leaf .projection
private theorem node_125_accepts : node_125.Accepts parameters box_125 := by
  norm_num [Tree.Accepts, node_125, box_125, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_123 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_123 : Tree := .splitD (15 / 32 : ℚ) node_124 node_125
private theorem node_123_accepts : node_123.Accepts parameters box_123 := by
  change SplitDValid box_123 (15 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_123], node_124_accepts, node_125_accepts⟩

private def box_119 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_119 : Tree := .splitC (35 / 96 : ℚ) node_120 node_123
private theorem node_119_accepts : node_119.Accepts parameters box_119 := by
  change SplitCValid box_119 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_119], node_120_accepts, node_123_accepts⟩

private def box_126 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (23 / 48 : ℚ), (1 / 2 : ℚ)⟩
private def node_126 : Tree := .leaf .projection
private theorem node_126_accepts : node_126.Accepts parameters box_126 := by
  norm_num [Tree.Accepts, node_126, box_126, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_118 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_118 : Tree := .splitD (23 / 48 : ℚ) node_119 node_126
private theorem node_118_accepts : node_118.Accepts parameters box_118 := by
  change SplitDValid box_118 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_118], node_119_accepts, node_126_accepts⟩

private def box_112 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_112 : Tree := .splitC (17 / 48 : ℚ) node_113 node_118
private theorem node_112_accepts : node_112.Accepts parameters box_112 := by
  change SplitCValid box_112 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_112], node_113_accepts, node_118_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_0 : Tree := .splitD (11 / 24 : ℚ) node_1 node_112
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_112_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C070
