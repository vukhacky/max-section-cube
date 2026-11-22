import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C028

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_5 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_5 : Tree := .leaf .projection
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_4 : Tree := .splitD (577 / 1536 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_8 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_7 : Tree := .splitD (577 / 1536 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitDValid box_7 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_3 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_3 : Tree := .splitC (533 / 1536 : ℚ) node_4 node_7
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (533 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_7_accepts⟩

private def box_12 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_11 : Tree := .splitD (193 / 512 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_15 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_15 : Tree := .leaf .projection
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_14 : Tree := .splitD (193 / 512 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitDValid box_14 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_10 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_10 : Tree := .splitC (533 / 1536 : ℚ) node_11 node_14
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitCValid box_10 (533 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_10], node_11_accepts, node_14_accepts⟩

private def box_2 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_2 : Tree := .splitD (289 / 768 : ℚ) node_3 node_10
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_10_accepts⟩

private def box_21 : Rectangle := ⟨(89 / 256 : ℚ), (1069 / 3072 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(1069 / 3072 : ℚ), (535 / 1536 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_20 : Tree := .splitC (1069 / 3072 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (1069 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_23 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_19 : Tree := .splitD (577 / 1536 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_26 : Rectangle := ⟨(535 / 1536 : ℚ), (357 / 1024 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(357 / 1024 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_25 : Tree := .splitC (357 / 1024 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitCValid box_25 (357 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_29 : Rectangle := ⟨(535 / 1536 : ℚ), (357 / 1024 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(357 / 1024 : ℚ), (67 / 192 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_28 : Tree := .splitC (357 / 1024 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitCValid box_28 (357 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_24 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_24 : Tree := .splitD (577 / 1536 : ℚ) node_25 node_28
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_28_accepts⟩

private def box_18 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_18 : Tree := .splitC (535 / 1536 : ℚ) node_19 node_24
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitCValid box_18 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_18], node_19_accepts, node_24_accepts⟩

private def box_33 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_32 : Tree := .splitD (193 / 512 : ℚ) node_33 node_34
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitDValid box_32 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_32], node_33_accepts, node_34_accepts⟩

private def box_36 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_37 : Tree := .leaf .projection
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  norm_num [Tree.Accepts, node_37, box_37, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_35 : Tree := .splitD (193 / 512 : ℚ) node_36 node_37
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitDValid box_35 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_35], node_36_accepts, node_37_accepts⟩

private def box_31 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_31 : Tree := .splitC (535 / 1536 : ℚ) node_32 node_35
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_35_accepts⟩

private def box_17 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_17 : Tree := .splitD (289 / 768 : ℚ) node_18 node_31
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitDValid box_17 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_17], node_18_accepts, node_31_accepts⟩

private def box_1 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_1 : Tree := .splitC (89 / 256 : ℚ) node_2 node_17
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (89 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_17_accepts⟩

private def box_42 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_41 : Tree := .splitD (581 / 1536 : ℚ) node_42 node_43
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitDValid box_41 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_41], node_42_accepts, node_43_accepts⟩

private def box_45 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_44 : Tree := .splitD (581 / 1536 : ℚ) node_45 node_46
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitDValid box_44 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_44], node_45_accepts, node_46_accepts⟩

private def box_40 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_40 : Tree := .splitC (533 / 1536 : ℚ) node_41 node_44
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitCValid box_40 (533 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_40], node_41_accepts, node_44_accepts⟩

private def box_49 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_48 : Tree := .splitD (583 / 1536 : ℚ) node_49 node_50
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitDValid box_48 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_48], node_49_accepts, node_50_accepts⟩

private def box_52 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_52 : Tree := .leaf .projection
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_53 : Tree := .leaf .projection
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_51 : Tree := .splitD (583 / 1536 : ℚ) node_52 node_53
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitDValid box_51 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_51], node_52_accepts, node_53_accepts⟩

private def box_47 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_47 : Tree := .splitC (533 / 1536 : ℚ) node_48 node_51
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitCValid box_47 (533 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_47], node_48_accepts, node_51_accepts⟩

private def box_39 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_39 : Tree := .splitD (97 / 256 : ℚ) node_40 node_47
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitDValid box_39 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_39], node_40_accepts, node_47_accepts⟩

private def box_57 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_56 : Tree := .splitD (581 / 1536 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitDValid box_56 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_60 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_60 : Tree := .leaf .projection
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_59 : Tree := .splitD (581 / 1536 : ℚ) node_60 node_61
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitDValid box_59 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_59], node_60_accepts, node_61_accepts⟩

private def box_55 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_55 : Tree := .splitC (535 / 1536 : ℚ) node_56 node_59
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitCValid box_55 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_55], node_56_accepts, node_59_accepts⟩

private def box_64 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_64 : Tree := .leaf .projection
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  norm_num [Tree.Accepts, node_64, box_64, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_65 : Tree := .leaf .projection
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_63 : Tree := .splitD (583 / 1536 : ℚ) node_64 node_65
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitDValid box_63 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_63], node_64_accepts, node_65_accepts⟩

private def box_67 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_67 : Tree := .leaf .projection
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_68 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_66 : Tree := .splitD (583 / 1536 : ℚ) node_67 node_68
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitDValid box_66 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_66], node_67_accepts, node_68_accepts⟩

private def box_62 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_62 : Tree := .splitC (535 / 1536 : ℚ) node_63 node_66
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitCValid box_62 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_62], node_63_accepts, node_66_accepts⟩

private def box_54 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_54 : Tree := .splitD (97 / 256 : ℚ) node_55 node_62
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitDValid box_54 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_54], node_55_accepts, node_62_accepts⟩

private def box_38 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_38 : Tree := .splitC (89 / 256 : ℚ) node_39 node_54
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitCValid box_38 (89 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_38], node_39_accepts, node_54_accepts⟩

private def box_0 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_0 : Tree := .splitD (145 / 384 : ℚ) node_1 node_38
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_38_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C028
