import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C056

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_6 : Rectangle := ⟨(71 / 192 : ℚ), (569 / 1536 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(569 / 1536 : ℚ), (95 / 256 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_5 : Tree := .splitC (569 / 1536 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (569 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_9 : Rectangle := ⟨(71 / 192 : ℚ), (569 / 1536 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(569 / 1536 : ℚ), (95 / 256 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_8 : Tree := .splitC (569 / 1536 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitCValid box_8 (569 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_4 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_4 : Tree := .splitD (99 / 256 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (99 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_13 : Rectangle := ⟨(95 / 256 : ℚ), (571 / 1536 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(571 / 1536 : ℚ), (143 / 384 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_12 : Tree := .splitC (571 / 1536 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_16 : Rectangle := ⟨(95 / 256 : ℚ), (571 / 1536 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(571 / 1536 : ℚ), (143 / 384 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_15 : Tree := .splitC (571 / 1536 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_11 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_11 : Tree := .splitD (99 / 256 : ℚ) node_12 node_15
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (99 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_15_accepts⟩

private def box_3 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_3 : Tree := .splitC (95 / 256 : ℚ) node_4 node_11
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_11_accepts⟩

private def box_21 : Rectangle := ⟨(71 / 192 : ℚ), (569 / 1536 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(569 / 1536 : ℚ), (95 / 256 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_20 : Tree := .splitC (569 / 1536 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (569 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_23 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (299 / 768 : ℚ), (25 / 64 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_19 : Tree := .splitD (299 / 768 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (299 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_25 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (299 / 768 : ℚ), (25 / 64 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_24 : Tree := .splitD (299 / 768 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (299 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_18 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_18 : Tree := .splitC (95 / 256 : ℚ) node_19 node_24
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitCValid box_18 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_18], node_19_accepts, node_24_accepts⟩

private def box_2 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_2 : Tree := .splitD (149 / 384 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_31 : Rectangle := ⟨(143 / 384 : ℚ), (191 / 512 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(191 / 512 : ℚ), (287 / 768 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_30 : Tree := .splitC (191 / 512 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitCValid box_30 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_33 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_29 : Tree := .splitD (99 / 256 : ℚ) node_30 node_33
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitDValid box_29 (99 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_29], node_30_accepts, node_33_accepts⟩

private def box_35 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_34 : Tree := .splitD (99 / 256 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (99 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_28 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_28 : Tree := .splitC (287 / 768 : ℚ) node_29 node_34
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitCValid box_28 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_28], node_29_accepts, node_34_accepts⟩

private def box_39 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (299 / 768 : ℚ), (25 / 64 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_38 : Tree := .splitD (299 / 768 : ℚ) node_39 node_40
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitDValid box_38 (299 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_38], node_39_accepts, node_40_accepts⟩

private def box_42 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (299 / 768 : ℚ), (25 / 64 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_41 : Tree := .splitD (299 / 768 : ℚ) node_42 node_43
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitDValid box_41 (299 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_41], node_42_accepts, node_43_accepts⟩

private def box_37 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_37 : Tree := .splitC (287 / 768 : ℚ) node_38 node_41
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitCValid box_37 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_37], node_38_accepts, node_41_accepts⟩

private def box_27 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_27 : Tree := .splitD (149 / 384 : ℚ) node_28 node_37
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitDValid box_27 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_27], node_28_accepts, node_37_accepts⟩

private def box_1 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_1 : Tree := .splitC (143 / 384 : ℚ) node_2 node_27
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_27_accepts⟩

private def box_48 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (25 / 64 : ℚ), (301 / 768 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (301 / 768 : ℚ), (151 / 384 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_47 : Tree := .splitD (301 / 768 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (301 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_51 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (25 / 64 : ℚ), (301 / 768 : ℚ)⟩
private def node_51 : Tree := .leaf .projection
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (301 / 768 : ℚ), (151 / 384 : ℚ)⟩
private def node_52 : Tree := .leaf .projection
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_50 : Tree := .splitD (301 / 768 : ℚ) node_51 node_52
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitDValid box_50 (301 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_50], node_51_accepts, node_52_accepts⟩

private def box_46 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_46 : Tree := .splitC (95 / 256 : ℚ) node_47 node_50
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_50_accepts⟩

private def box_55 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (151 / 384 : ℚ), (101 / 256 : ℚ)⟩
private def node_55 : Tree := .leaf .projection
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (101 / 256 : ℚ), (19 / 48 : ℚ)⟩
private def node_56 : Tree := .leaf .projection
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(71 / 192 : ℚ), (95 / 256 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_54 : Tree := .splitD (101 / 256 : ℚ) node_55 node_56
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitDValid box_54 (101 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_54], node_55_accepts, node_56_accepts⟩

private def box_58 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (151 / 384 : ℚ), (101 / 256 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (101 / 256 : ℚ), (19 / 48 : ℚ)⟩
private def node_59 : Tree := .leaf .projection
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(95 / 256 : ℚ), (143 / 384 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_57 : Tree := .splitD (101 / 256 : ℚ) node_58 node_59
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitDValid box_57 (101 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_57], node_58_accepts, node_59_accepts⟩

private def box_53 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_53 : Tree := .splitC (95 / 256 : ℚ) node_54 node_57
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitCValid box_53 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_53], node_54_accepts, node_57_accepts⟩

private def box_45 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_45 : Tree := .splitD (151 / 384 : ℚ) node_46 node_53
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitDValid box_45 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_45], node_46_accepts, node_53_accepts⟩

private def box_63 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (25 / 64 : ℚ), (301 / 768 : ℚ)⟩
private def node_63 : Tree := .leaf .projection
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (301 / 768 : ℚ), (151 / 384 : ℚ)⟩
private def node_64 : Tree := .leaf .projection
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  norm_num [Tree.Accepts, node_64, box_64, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_62 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_62 : Tree := .splitD (301 / 768 : ℚ) node_63 node_64
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitDValid box_62 (301 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_62], node_63_accepts, node_64_accepts⟩

private def box_66 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (25 / 64 : ℚ), (301 / 768 : ℚ)⟩
private def node_66 : Tree := .leaf .projection
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (301 / 768 : ℚ), (151 / 384 : ℚ)⟩
private def node_67 : Tree := .leaf .projection
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_65 : Tree := .splitD (301 / 768 : ℚ) node_66 node_67
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitDValid box_65 (301 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_65], node_66_accepts, node_67_accepts⟩

private def box_61 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_61 : Tree := .splitC (287 / 768 : ℚ) node_62 node_65
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitCValid box_61 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_61], node_62_accepts, node_65_accepts⟩

private def box_70 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (151 / 384 : ℚ), (101 / 256 : ℚ)⟩
private def node_70 : Tree := .leaf .projection
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  norm_num [Tree.Accepts, node_70, box_70, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (101 / 256 : ℚ), (19 / 48 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(143 / 384 : ℚ), (287 / 768 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_69 : Tree := .splitD (101 / 256 : ℚ) node_70 node_71
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  change SplitDValid box_69 (101 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_69], node_70_accepts, node_71_accepts⟩

private def box_73 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (151 / 384 : ℚ), (101 / 256 : ℚ)⟩
private def node_73 : Tree := .leaf .projection
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  norm_num [Tree.Accepts, node_73, box_73, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (101 / 256 : ℚ), (19 / 48 : ℚ)⟩
private def node_74 : Tree := .leaf .projection
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  norm_num [Tree.Accepts, node_74, box_74, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(287 / 768 : ℚ), (3 / 8 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_72 : Tree := .splitD (101 / 256 : ℚ) node_73 node_74
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitDValid box_72 (101 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_72], node_73_accepts, node_74_accepts⟩

private def box_68 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_68 : Tree := .splitC (287 / 768 : ℚ) node_69 node_72
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  change SplitCValid box_68 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_68], node_69_accepts, node_72_accepts⟩

private def box_60 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_60 : Tree := .splitD (151 / 384 : ℚ) node_61 node_68
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitDValid box_60 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_60], node_61_accepts, node_68_accepts⟩

private def box_44 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_44 : Tree := .splitC (143 / 384 : ℚ) node_45 node_60
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_60_accepts⟩

private def box_0 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_0 : Tree := .splitD (25 / 64 : ℚ) node_1 node_44
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_44_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C056
