import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C029

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_5 : Rectangle := ⟨(11 / 32 : ℚ), (529 / 1536 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_5 : Tree := .leaf .projection
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(529 / 1536 : ℚ), (265 / 768 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_4 : Tree := .splitC (529 / 1536 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (529 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_7 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_3 : Tree := .splitD (293 / 768 : ℚ) node_4 node_7
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_7_accepts⟩

private def box_10 : Rectangle := ⟨(265 / 768 : ℚ), (177 / 512 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(177 / 512 : ℚ), (133 / 384 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_9 : Tree := .splitC (177 / 512 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (177 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_13 : Rectangle := ⟨(265 / 768 : ℚ), (177 / 512 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(177 / 512 : ℚ), (133 / 384 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_12 : Tree := .splitC (177 / 512 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (177 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_8 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_8 : Tree := .splitD (293 / 768 : ℚ) node_9 node_12
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_12_accepts⟩

private def box_2 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_2 : Tree := .splitC (265 / 768 : ℚ) node_3 node_8
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (265 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_8_accepts⟩

private def box_17 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_16 : Tree := .splitD (295 / 768 : ℚ) node_17 node_18
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_18_accepts⟩

private def box_20 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_19 : Tree := .splitD (295 / 768 : ℚ) node_20 node_21
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_21_accepts⟩

private def box_15 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_15 : Tree := .splitC (265 / 768 : ℚ) node_16 node_19
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (265 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_19_accepts⟩

private def box_1 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_1 : Tree := .splitD (49 / 128 : ℚ) node_2 node_15
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_15_accepts⟩

private def box_27 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_26 : Tree := .splitD (195 / 512 : ℚ) node_27 node_28
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitDValid box_26 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_26], node_27_accepts, node_28_accepts⟩

private def box_30 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_29 : Tree := .splitD (195 / 512 : ℚ) node_30 node_31
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitDValid box_29 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_29], node_30_accepts, node_31_accepts⟩

private def box_25 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_25 : Tree := .splitC (533 / 1536 : ℚ) node_26 node_29
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitCValid box_25 (533 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_25], node_26_accepts, node_29_accepts⟩

private def box_33 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_32 : Tree := .splitC (533 / 1536 : ℚ) node_33 node_34
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitCValid box_32 (533 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_32], node_33_accepts, node_34_accepts⟩

private def box_24 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_24 : Tree := .splitD (293 / 768 : ℚ) node_25 node_32
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_32_accepts⟩

private def box_38 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_37 : Tree := .splitD (195 / 512 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_41 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_40 : Tree := .splitD (195 / 512 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_36 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_36 : Tree := .splitC (535 / 1536 : ℚ) node_37 node_40
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitCValid box_36 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_36], node_37_accepts, node_40_accepts⟩

private def box_45 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_44 : Tree := .splitD (587 / 1536 : ℚ) node_45 node_46
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitDValid box_44 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_44], node_45_accepts, node_46_accepts⟩

private def box_48 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_47 : Tree := .splitD (587 / 1536 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_43 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_43 : Tree := .splitC (535 / 1536 : ℚ) node_44 node_47
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitCValid box_43 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_43], node_44_accepts, node_47_accepts⟩

private def box_35 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_35 : Tree := .splitD (293 / 768 : ℚ) node_36 node_43
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitDValid box_35 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_35], node_36_accepts, node_43_accepts⟩

private def box_23 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_23 : Tree := .splitC (89 / 256 : ℚ) node_24 node_35
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitCValid box_23 (89 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_23], node_24_accepts, node_35_accepts⟩

private def box_53 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_53 : Tree := .leaf .projection
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_52 : Tree := .splitC (533 / 1536 : ℚ) node_53 node_54
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitCValid box_52 (533 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_52], node_53_accepts, node_54_accepts⟩

private def box_55 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_55 : Tree := .leaf .projection
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_51 : Tree := .splitD (295 / 768 : ℚ) node_52 node_55
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitDValid box_51 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_51], node_52_accepts, node_55_accepts⟩

private def box_58 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_59 : Tree := .leaf .projection
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_57 : Tree := .splitC (535 / 1536 : ℚ) node_58 node_59
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitCValid box_57 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_57], node_58_accepts, node_59_accepts⟩

private def box_61 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_62 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_62 : Tree := .leaf .projection
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_60 : Tree := .splitC (535 / 1536 : ℚ) node_61 node_62
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitCValid box_60 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_60], node_61_accepts, node_62_accepts⟩

private def box_56 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_56 : Tree := .splitD (295 / 768 : ℚ) node_57 node_60
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitDValid box_56 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_56], node_57_accepts, node_60_accepts⟩

private def box_50 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_50 : Tree := .splitC (89 / 256 : ℚ) node_51 node_56
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitCValid box_50 (89 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_50], node_51_accepts, node_56_accepts⟩

private def box_22 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_22 : Tree := .splitD (49 / 128 : ℚ) node_23 node_50
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitDValid box_22 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_22], node_23_accepts, node_50_accepts⟩

private def box_0 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_0 : Tree := .splitC (133 / 384 : ℚ) node_1 node_22
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (133 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_22_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C029
