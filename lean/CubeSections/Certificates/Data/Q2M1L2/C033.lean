import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C033

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_6 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_5 : Tree := .splitD (195 / 512 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_9 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_8 : Tree := .splitD (195 / 512 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_4 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_4 : Tree := .splitC (179 / 512 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_13 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_12 : Tree := .splitD (587 / 1536 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_16 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_15 : Tree := .splitD (587 / 1536 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_11 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_11 : Tree := .splitC (179 / 512 : ℚ) node_12 node_15
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitCValid box_11 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_11], node_12_accepts, node_15_accepts⟩

private def box_3 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_3 : Tree := .splitD (293 / 768 : ℚ) node_4 node_11
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_11_accepts⟩

private def box_21 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_20 : Tree := .splitD (195 / 512 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_24 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_24 : Tree := .leaf .projection
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_23 : Tree := .splitD (195 / 512 : ℚ) node_24 node_25
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitDValid box_23 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_23], node_24_accepts, node_25_accepts⟩

private def box_19 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_19 : Tree := .splitC (539 / 1536 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitCValid box_19 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_28 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_27 : Tree := .splitD (587 / 1536 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitDValid box_27 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_31 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_30 : Tree := .splitD (587 / 1536 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_26 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_26 : Tree := .splitC (539 / 1536 : ℚ) node_27 node_30
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitCValid box_26 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_26], node_27_accepts, node_30_accepts⟩

private def box_18 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_18 : Tree := .splitD (293 / 768 : ℚ) node_19 node_26
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_26_accepts⟩

private def box_2 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_2 : Tree := .splitC (269 / 768 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_36 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (49 / 128 : ℚ), (589 / 1536 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (589 / 1536 : ℚ), (295 / 768 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_37 : Tree := .splitD (589 / 1536 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (589 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_35 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_35 : Tree := .splitC (179 / 512 : ℚ) node_36 node_37
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitCValid box_35 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_35], node_36_accepts, node_37_accepts⟩

private def box_41 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_40 : Tree := .splitC (179 / 512 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitCValid box_40 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_34 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_34 : Tree := .splitD (295 / 768 : ℚ) node_35 node_40
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_40_accepts⟩

private def box_46 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (49 / 128 : ℚ), (589 / 1536 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (589 / 1536 : ℚ), (295 / 768 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_45 : Tree := .splitD (589 / 1536 : ℚ) node_46 node_47
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitDValid box_45 (589 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_45], node_46_accepts, node_47_accepts⟩

private def box_49 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (49 / 128 : ℚ), (589 / 1536 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (589 / 1536 : ℚ), (295 / 768 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_48 : Tree := .splitD (589 / 1536 : ℚ) node_49 node_50
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitDValid box_48 (589 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_48], node_49_accepts, node_50_accepts⟩

private def box_44 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_44 : Tree := .splitC (539 / 1536 : ℚ) node_45 node_48
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_48_accepts⟩

private def box_52 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_52 : Tree := .leaf .projection
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_53 : Tree := .leaf .projection
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_51 : Tree := .splitC (539 / 1536 : ℚ) node_52 node_53
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitCValid box_51 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_51], node_52_accepts, node_53_accepts⟩

private def box_43 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_43 : Tree := .splitD (295 / 768 : ℚ) node_44 node_51
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_51_accepts⟩

private def box_33 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_33 : Tree := .splitC (269 / 768 : ℚ) node_34 node_43
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitCValid box_33 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_33], node_34_accepts, node_43_accepts⟩

private def box_1 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_1 : Tree := .splitD (49 / 128 : ℚ) node_2 node_33
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_33_accepts⟩

private def box_59 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_59 : Tree := .leaf .projection
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_60 : Tree := .leaf .projection
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_58 : Tree := .splitD (195 / 512 : ℚ) node_59 node_60
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  change SplitDValid box_58 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_58], node_59_accepts, node_60_accepts⟩

private def box_62 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_62 : Tree := .leaf .projection
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_63 : Tree := .leaf .projection
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_61 : Tree := .splitD (195 / 512 : ℚ) node_62 node_63
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitDValid box_61 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_61], node_62_accepts, node_63_accepts⟩

private def box_57 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_57 : Tree := .splitC (541 / 1536 : ℚ) node_58 node_61
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitCValid box_57 (541 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_57], node_58_accepts, node_61_accepts⟩

private def box_66 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_66 : Tree := .leaf .projection
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_67 : Tree := .leaf .projection
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_65 : Tree := .splitD (587 / 1536 : ℚ) node_66 node_67
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitDValid box_65 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_65], node_66_accepts, node_67_accepts⟩

private def box_69 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_69 : Tree := .leaf .projection
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_70 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_70 : Tree := .leaf .projection
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  norm_num [Tree.Accepts, node_70, box_70, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_68 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_68 : Tree := .splitD (587 / 1536 : ℚ) node_69 node_70
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  change SplitDValid box_68 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_68], node_69_accepts, node_70_accepts⟩

private def box_64 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_64 : Tree := .splitC (541 / 1536 : ℚ) node_65 node_68
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitCValid box_64 (541 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_64], node_65_accepts, node_68_accepts⟩

private def box_56 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_56 : Tree := .splitD (293 / 768 : ℚ) node_57 node_64
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitDValid box_56 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_56], node_57_accepts, node_64_accepts⟩

private def box_74 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_74 : Tree := .leaf .projection
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  norm_num [Tree.Accepts, node_74, box_74, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_75 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_73 : Tree := .splitD (195 / 512 : ℚ) node_74 node_75
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitDValid box_73 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_73], node_74_accepts, node_75_accepts⟩

private def box_77 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (73 / 192 : ℚ), (195 / 512 : ℚ)⟩
private def node_77 : Tree := .leaf .projection
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  norm_num [Tree.Accepts, node_77, box_77, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (195 / 512 : ℚ), (293 / 768 : ℚ)⟩
private def node_78 : Tree := .leaf .projection
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_76 : Tree := .splitD (195 / 512 : ℚ) node_77 node_78
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  change SplitDValid box_76 (195 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_76], node_77_accepts, node_78_accepts⟩

private def box_72 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_72 : Tree := .splitC (181 / 512 : ℚ) node_73 node_76
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitCValid box_72 (181 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_72], node_73_accepts, node_76_accepts⟩

private def box_81 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_81 : Tree := .leaf .projection
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  norm_num [Tree.Accepts, node_81, box_81, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_82 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_82 : Tree := .leaf .projection
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_80 : Tree := .splitD (587 / 1536 : ℚ) node_81 node_82
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitDValid box_80 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_80], node_81_accepts, node_82_accepts⟩

private def box_84 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (293 / 768 : ℚ), (587 / 1536 : ℚ)⟩
private def node_84 : Tree := .leaf .projection
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  norm_num [Tree.Accepts, node_84, box_84, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_85 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (587 / 1536 : ℚ), (49 / 128 : ℚ)⟩
private def node_85 : Tree := .leaf .projection
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  norm_num [Tree.Accepts, node_85, box_85, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_83 : Tree := .splitD (587 / 1536 : ℚ) node_84 node_85
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  change SplitDValid box_83 (587 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_83], node_84_accepts, node_85_accepts⟩

private def box_79 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_79 : Tree := .splitC (181 / 512 : ℚ) node_80 node_83
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  change SplitCValid box_79 (181 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_79], node_80_accepts, node_83_accepts⟩

private def box_71 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_71 : Tree := .splitD (293 / 768 : ℚ) node_72 node_79
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  change SplitDValid box_71 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_71], node_72_accepts, node_79_accepts⟩

private def box_55 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_55 : Tree := .splitC (271 / 768 : ℚ) node_56 node_71
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitCValid box_55 (271 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_55], node_56_accepts, node_71_accepts⟩

private def box_90 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (49 / 128 : ℚ), (589 / 1536 : ℚ)⟩
private def node_90 : Tree := .leaf .projection
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  norm_num [Tree.Accepts, node_90, box_90, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_91 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (589 / 1536 : ℚ), (295 / 768 : ℚ)⟩
private def node_91 : Tree := .leaf .projection
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  norm_num [Tree.Accepts, node_91, box_91, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_89 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_89 : Tree := .splitD (589 / 1536 : ℚ) node_90 node_91
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  change SplitDValid box_89 (589 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_89], node_90_accepts, node_91_accepts⟩

private def box_93 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (49 / 128 : ℚ), (589 / 1536 : ℚ)⟩
private def node_93 : Tree := .leaf .projection
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  norm_num [Tree.Accepts, node_93, box_93, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (589 / 1536 : ℚ), (295 / 768 : ℚ)⟩
private def node_94 : Tree := .leaf .projection
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  norm_num [Tree.Accepts, node_94, box_94, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_92 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_92 : Tree := .splitD (589 / 1536 : ℚ) node_93 node_94
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  change SplitDValid box_92 (589 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_92], node_93_accepts, node_94_accepts⟩

private def box_88 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_88 : Tree := .splitC (541 / 1536 : ℚ) node_89 node_92
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  change SplitCValid box_88 (541 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_88], node_89_accepts, node_92_accepts⟩

private def box_97 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (295 / 768 : ℚ), (197 / 512 : ℚ)⟩
private def node_97 : Tree := .leaf .projection
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  norm_num [Tree.Accepts, node_97, box_97, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_98 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (197 / 512 : ℚ), (37 / 96 : ℚ)⟩
private def node_98 : Tree := .leaf .projection
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  norm_num [Tree.Accepts, node_98, box_98, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_96 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_96 : Tree := .splitD (197 / 512 : ℚ) node_97 node_98
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  change SplitDValid box_96 (197 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_96], node_97_accepts, node_98_accepts⟩

private def box_100 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (295 / 768 : ℚ), (197 / 512 : ℚ)⟩
private def node_100 : Tree := .leaf .projection
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  norm_num [Tree.Accepts, node_100, box_100, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_101 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (197 / 512 : ℚ), (37 / 96 : ℚ)⟩
private def node_101 : Tree := .leaf .projection
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  norm_num [Tree.Accepts, node_101, box_101, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_99 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_99 : Tree := .splitD (197 / 512 : ℚ) node_100 node_101
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  change SplitDValid box_99 (197 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_99], node_100_accepts, node_101_accepts⟩

private def box_95 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_95 : Tree := .splitC (541 / 1536 : ℚ) node_96 node_99
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  change SplitCValid box_95 (541 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_95], node_96_accepts, node_99_accepts⟩

private def box_87 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_87 : Tree := .splitD (295 / 768 : ℚ) node_88 node_95
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  change SplitDValid box_87 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_87], node_88_accepts, node_95_accepts⟩

private def box_105 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (49 / 128 : ℚ), (589 / 1536 : ℚ)⟩
private def node_105 : Tree := .leaf .projection
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  norm_num [Tree.Accepts, node_105, box_105, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_106 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (589 / 1536 : ℚ), (295 / 768 : ℚ)⟩
private def node_106 : Tree := .leaf .projection
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  norm_num [Tree.Accepts, node_106, box_106, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_104 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_104 : Tree := .splitD (589 / 1536 : ℚ) node_105 node_106
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  change SplitDValid box_104 (589 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_104], node_105_accepts, node_106_accepts⟩

private def box_108 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (49 / 128 : ℚ), (589 / 1536 : ℚ)⟩
private def node_108 : Tree := .leaf .projection
private theorem node_108_accepts : node_108.Accepts parameters box_108 := by
  norm_num [Tree.Accepts, node_108, box_108, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_109 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (589 / 1536 : ℚ), (295 / 768 : ℚ)⟩
private def node_109 : Tree := .leaf .projection
private theorem node_109_accepts : node_109.Accepts parameters box_109 := by
  norm_num [Tree.Accepts, node_109, box_109, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_107 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_107 : Tree := .splitD (589 / 1536 : ℚ) node_108 node_109
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  change SplitDValid box_107 (589 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_107], node_108_accepts, node_109_accepts⟩

private def box_103 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_103 : Tree := .splitC (181 / 512 : ℚ) node_104 node_107
private theorem node_103_accepts : node_103.Accepts parameters box_103 := by
  change SplitCValid box_103 (181 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_103], node_104_accepts, node_107_accepts⟩

private def box_112 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (295 / 768 : ℚ), (197 / 512 : ℚ)⟩
private def node_112 : Tree := .leaf .projection
private theorem node_112_accepts : node_112.Accepts parameters box_112 := by
  norm_num [Tree.Accepts, node_112, box_112, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_113 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (197 / 512 : ℚ), (37 / 96 : ℚ)⟩
private def node_113 : Tree := .leaf .projection
private theorem node_113_accepts : node_113.Accepts parameters box_113 := by
  norm_num [Tree.Accepts, node_113, box_113, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_111 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_111 : Tree := .splitD (197 / 512 : ℚ) node_112 node_113
private theorem node_111_accepts : node_111.Accepts parameters box_111 := by
  change SplitDValid box_111 (197 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_111], node_112_accepts, node_113_accepts⟩

private def box_115 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (295 / 768 : ℚ), (197 / 512 : ℚ)⟩
private def node_115 : Tree := .leaf .projection
private theorem node_115_accepts : node_115.Accepts parameters box_115 := by
  norm_num [Tree.Accepts, node_115, box_115, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_116 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (197 / 512 : ℚ), (37 / 96 : ℚ)⟩
private def node_116 : Tree := .leaf .projection
private theorem node_116_accepts : node_116.Accepts parameters box_116 := by
  norm_num [Tree.Accepts, node_116, box_116, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_114 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_114 : Tree := .splitD (197 / 512 : ℚ) node_115 node_116
private theorem node_114_accepts : node_114.Accepts parameters box_114 := by
  change SplitDValid box_114 (197 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_114], node_115_accepts, node_116_accepts⟩

private def box_110 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_110 : Tree := .splitC (181 / 512 : ℚ) node_111 node_114
private theorem node_110_accepts : node_110.Accepts parameters box_110 := by
  change SplitCValid box_110 (181 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_110], node_111_accepts, node_114_accepts⟩

private def box_102 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_102 : Tree := .splitD (295 / 768 : ℚ) node_103 node_110
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  change SplitDValid box_102 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_102], node_103_accepts, node_110_accepts⟩

private def box_86 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_86 : Tree := .splitC (271 / 768 : ℚ) node_87 node_102
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  change SplitCValid box_86 (271 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_86], node_87_accepts, node_102_accepts⟩

private def box_54 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_54 : Tree := .splitD (49 / 128 : ℚ) node_55 node_86
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitDValid box_54 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_54], node_55_accepts, node_86_accepts⟩

private def box_0 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_0 : Tree := .splitC (45 / 128 : ℚ) node_1 node_54
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_54_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C033
