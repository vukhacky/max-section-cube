import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C038

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_5 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_5 : Tree := .leaf .projection
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_4 : Tree := .splitC (363 / 1024 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (363 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_8 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_7 : Tree := .splitC (363 / 1024 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitCValid box_7 (363 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_3 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_3 : Tree := .splitD (581 / 1536 : ℚ) node_4 node_7
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_7_accepts⟩

private def box_12 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_11 : Tree := .splitC (1091 / 3072 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitCValid box_11 (1091 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_15 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_15 : Tree := .leaf .projection
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_14 : Tree := .splitC (1091 / 3072 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitCValid box_14 (1091 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_10 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_10 : Tree := .splitD (581 / 1536 : ℚ) node_11 node_14
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitDValid box_10 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_10], node_11_accepts, node_14_accepts⟩

private def box_2 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_2 : Tree := .splitC (545 / 1536 : ℚ) node_3 node_10
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (545 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_10_accepts⟩

private def box_20 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_19 : Tree := .splitC (363 / 1024 : ℚ) node_20 node_21
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitCValid box_19 (363 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_19], node_20_accepts, node_21_accepts⟩

private def box_22 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_18 : Tree := .splitD (583 / 1536 : ℚ) node_19 node_22
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_22_accepts⟩

private def box_25 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_24 : Tree := .splitC (1091 / 3072 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (1091 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_27 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_23 : Tree := .splitD (583 / 1536 : ℚ) node_24 node_27
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitDValid box_23 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_23], node_24_accepts, node_27_accepts⟩

private def box_17 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_17 : Tree := .splitC (545 / 1536 : ℚ) node_18 node_23
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitCValid box_17 (545 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_17], node_18_accepts, node_23_accepts⟩

private def box_1 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_1 : Tree := .splitD (97 / 256 : ℚ) node_2 node_17
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_17_accepts⟩

private def box_32 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_31 : Tree := .splitC (1093 / 3072 : ℚ) node_32 node_33
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (1093 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_33_accepts⟩

private def box_35 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_34 : Tree := .splitC (1093 / 3072 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitCValid box_34 (1093 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_30 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_30 : Tree := .splitD (581 / 1536 : ℚ) node_31 node_34
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_34_accepts⟩

private def box_39 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_38 : Tree := .splitC (365 / 1024 : ℚ) node_39 node_40
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitCValid box_38 (365 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_38], node_39_accepts, node_40_accepts⟩

private def box_42 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_41 : Tree := .splitC (365 / 1024 : ℚ) node_42 node_43
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitCValid box_41 (365 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_41], node_42_accepts, node_43_accepts⟩

private def box_37 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_37 : Tree := .splitD (581 / 1536 : ℚ) node_38 node_41
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_41_accepts⟩

private def box_29 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_29 : Tree := .splitC (547 / 1536 : ℚ) node_30 node_37
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitCValid box_29 (547 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_29], node_30_accepts, node_37_accepts⟩

private def box_47 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_46 : Tree := .splitC (1093 / 3072 : ℚ) node_47 node_48
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (1093 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_48_accepts⟩

private def box_50 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_51 : Tree := .leaf .projection
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_49 : Tree := .splitC (1093 / 3072 : ℚ) node_50 node_51
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitCValid box_49 (1093 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_49], node_50_accepts, node_51_accepts⟩

private def box_45 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_45 : Tree := .splitD (583 / 1536 : ℚ) node_46 node_49
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitDValid box_45 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_45], node_46_accepts, node_49_accepts⟩

private def box_54 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_55 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_55 : Tree := .leaf .projection
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_53 : Tree := .splitC (365 / 1024 : ℚ) node_54 node_55
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitCValid box_53 (365 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_53], node_54_accepts, node_55_accepts⟩

private def box_57 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_56 : Tree := .splitC (365 / 1024 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitCValid box_56 (365 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_52 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_52 : Tree := .splitD (583 / 1536 : ℚ) node_53 node_56
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitDValid box_52 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_52], node_53_accepts, node_56_accepts⟩

private def box_44 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_44 : Tree := .splitC (547 / 1536 : ℚ) node_45 node_52
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (547 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_52_accepts⟩

private def box_28 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_28 : Tree := .splitD (97 / 256 : ℚ) node_29 node_44
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_44_accepts⟩

private def box_0 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_0 : Tree := .splitC (91 / 256 : ℚ) node_1 node_28
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (91 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_28_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C038
