import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C030

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_6 : Rectangle := ⟨(67 / 192 : ℚ), (1073 / 3072 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(1073 / 3072 : ℚ), (179 / 512 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_5 : Tree := .splitC (1073 / 3072 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (1073 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_9 : Rectangle := ⟨(67 / 192 : ℚ), (1073 / 3072 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(1073 / 3072 : ℚ), (179 / 512 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_8 : Tree := .splitC (1073 / 3072 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitCValid box_8 (1073 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_4 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_4 : Tree := .splitD (577 / 1536 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_13 : Rectangle := ⟨(179 / 512 : ℚ), (1075 / 3072 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(1075 / 3072 : ℚ), (269 / 768 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_12 : Tree := .splitC (1075 / 3072 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (1075 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_16 : Rectangle := ⟨(179 / 512 : ℚ), (1075 / 3072 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(1075 / 3072 : ℚ), (269 / 768 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_15 : Tree := .splitC (1075 / 3072 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (1075 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_11 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_11 : Tree := .splitD (577 / 1536 : ℚ) node_12 node_15
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_15_accepts⟩

private def box_3 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_3 : Tree := .splitC (179 / 512 : ℚ) node_4 node_11
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_11_accepts⟩

private def box_21 : Rectangle := ⟨(67 / 192 : ℚ), (1073 / 3072 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(1073 / 3072 : ℚ), (179 / 512 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_20 : Tree := .splitC (1073 / 3072 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (1073 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_23 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_19 : Tree := .splitD (193 / 512 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_26 : Rectangle := ⟨(179 / 512 : ℚ), (1075 / 3072 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(1075 / 3072 : ℚ), (269 / 768 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_25 : Tree := .splitC (1075 / 3072 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitCValid box_25 (1075 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_28 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_24 : Tree := .splitD (193 / 512 : ℚ) node_25 node_28
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_28_accepts⟩

private def box_18 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_18 : Tree := .splitC (179 / 512 : ℚ) node_19 node_24
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitCValid box_18 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_18], node_19_accepts, node_24_accepts⟩

private def box_2 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_2 : Tree := .splitD (289 / 768 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_34 : Rectangle := ⟨(269 / 768 : ℚ), (359 / 1024 : ℚ), (3 / 8 : ℚ), (1153 / 3072 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(269 / 768 : ℚ), (359 / 1024 : ℚ), (1153 / 3072 : ℚ), (577 / 1536 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(269 / 768 : ℚ), (359 / 1024 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_33 : Tree := .splitD (1153 / 3072 : ℚ) node_34 node_35
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (1153 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_35_accepts⟩

private def box_37 : Rectangle := ⟨(359 / 1024 : ℚ), (539 / 1536 : ℚ), (3 / 8 : ℚ), (1153 / 3072 : ℚ)⟩
private def node_37 : Tree := .leaf .projection
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  norm_num [Tree.Accepts, node_37, box_37, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(359 / 1024 : ℚ), (539 / 1536 : ℚ), (1153 / 3072 : ℚ), (577 / 1536 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(359 / 1024 : ℚ), (539 / 1536 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_36 : Tree := .splitD (1153 / 3072 : ℚ) node_37 node_38
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitDValid box_36 (1153 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_36], node_37_accepts, node_38_accepts⟩

private def box_32 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_32 : Tree := .splitC (359 / 1024 : ℚ) node_33 node_36
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitCValid box_32 (359 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_32], node_33_accepts, node_36_accepts⟩

private def box_40 : Rectangle := ⟨(269 / 768 : ℚ), (359 / 1024 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(359 / 1024 : ℚ), (539 / 1536 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_39 : Tree := .splitC (359 / 1024 : ℚ) node_40 node_41
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitCValid box_39 (359 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_39], node_40_accepts, node_41_accepts⟩

private def box_31 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_31 : Tree := .splitD (577 / 1536 : ℚ) node_32 node_39
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitDValid box_31 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_31], node_32_accepts, node_39_accepts⟩

private def box_45 : Rectangle := ⟨(539 / 1536 : ℚ), (1079 / 3072 : ℚ), (3 / 8 : ℚ), (1153 / 3072 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(539 / 1536 : ℚ), (1079 / 3072 : ℚ), (1153 / 3072 : ℚ), (577 / 1536 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(539 / 1536 : ℚ), (1079 / 3072 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_44 : Tree := .splitD (1153 / 3072 : ℚ) node_45 node_46
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitDValid box_44 (1153 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_44], node_45_accepts, node_46_accepts⟩

private def box_48 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (1153 / 3072 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (1153 / 3072 : ℚ), (577 / 1536 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_47 : Tree := .splitD (1153 / 3072 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (1153 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_43 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_43 : Tree := .splitC (1079 / 3072 : ℚ) node_44 node_47
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitCValid box_43 (1079 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_43], node_44_accepts, node_47_accepts⟩

private def box_51 : Rectangle := ⟨(539 / 1536 : ℚ), (1079 / 3072 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_51 : Tree := .leaf .projection
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (577 / 1536 : ℚ), (385 / 1024 : ℚ)⟩
private def node_53 : Tree := .leaf .projection
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (385 / 1024 : ℚ), (289 / 768 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_52 : Tree := .splitD (385 / 1024 : ℚ) node_53 node_54
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitDValid box_52 (385 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_52], node_53_accepts, node_54_accepts⟩

private def box_50 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_50 : Tree := .splitC (1079 / 3072 : ℚ) node_51 node_52
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitCValid box_50 (1079 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_50], node_51_accepts, node_52_accepts⟩

private def box_42 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_42 : Tree := .splitD (577 / 1536 : ℚ) node_43 node_50
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitDValid box_42 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_42], node_43_accepts, node_50_accepts⟩

private def box_30 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_30 : Tree := .splitC (539 / 1536 : ℚ) node_31 node_42
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitCValid box_30 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_30], node_31_accepts, node_42_accepts⟩

private def box_58 : Rectangle := ⟨(269 / 768 : ℚ), (359 / 1024 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(359 / 1024 : ℚ), (539 / 1536 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_59 : Tree := .leaf .projection
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_57 : Tree := .splitC (359 / 1024 : ℚ) node_58 node_59
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitCValid box_57 (359 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_57], node_58_accepts, node_59_accepts⟩

private def box_61 : Rectangle := ⟨(269 / 768 : ℚ), (359 / 1024 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_62 : Rectangle := ⟨(359 / 1024 : ℚ), (539 / 1536 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_62 : Tree := .leaf .projection
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_60 : Tree := .splitC (359 / 1024 : ℚ) node_61 node_62
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitCValid box_60 (359 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_60], node_61_accepts, node_62_accepts⟩

private def box_56 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_56 : Tree := .splitD (193 / 512 : ℚ) node_57 node_60
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitDValid box_56 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_56], node_57_accepts, node_60_accepts⟩

private def box_65 : Rectangle := ⟨(539 / 1536 : ℚ), (1079 / 3072 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_65 : Tree := .leaf .projection
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_66 : Tree := .leaf .projection
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_64 : Tree := .splitC (1079 / 3072 : ℚ) node_65 node_66
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitCValid box_64 (1079 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_64], node_65_accepts, node_66_accepts⟩

private def box_68 : Rectangle := ⟨(539 / 1536 : ℚ), (1079 / 3072 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_69 : Tree := .leaf .projection
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_67 : Tree := .splitC (1079 / 3072 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitCValid box_67 (1079 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_63 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_63 : Tree := .splitD (193 / 512 : ℚ) node_64 node_67
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitDValid box_63 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_63], node_64_accepts, node_67_accepts⟩

private def box_55 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_55 : Tree := .splitC (539 / 1536 : ℚ) node_56 node_63
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitCValid box_55 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_55], node_56_accepts, node_63_accepts⟩

private def box_29 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_29 : Tree := .splitD (289 / 768 : ℚ) node_30 node_55
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitDValid box_29 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_29], node_30_accepts, node_55_accepts⟩

private def box_1 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_1 : Tree := .splitC (269 / 768 : ℚ) node_2 node_29
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_29_accepts⟩

private def box_74 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_74 : Tree := .leaf .projection
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  norm_num [Tree.Accepts, node_74, box_74, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_75 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_73 : Tree := .splitD (581 / 1536 : ℚ) node_74 node_75
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitDValid box_73 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_73], node_74_accepts, node_75_accepts⟩

private def box_77 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_77 : Tree := .leaf .projection
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  norm_num [Tree.Accepts, node_77, box_77, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_78 : Tree := .leaf .projection
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_76 : Tree := .splitD (581 / 1536 : ℚ) node_77 node_78
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  change SplitDValid box_76 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_76], node_77_accepts, node_78_accepts⟩

private def box_72 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_72 : Tree := .splitC (179 / 512 : ℚ) node_73 node_76
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitCValid box_72 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_72], node_73_accepts, node_76_accepts⟩

private def box_81 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_81 : Tree := .leaf .projection
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  norm_num [Tree.Accepts, node_81, box_81, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_82 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_82 : Tree := .leaf .projection
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_80 : Tree := .splitD (583 / 1536 : ℚ) node_81 node_82
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitDValid box_80 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_80], node_81_accepts, node_82_accepts⟩

private def box_84 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_84 : Tree := .leaf .projection
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  norm_num [Tree.Accepts, node_84, box_84, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_85 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_85 : Tree := .leaf .projection
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  norm_num [Tree.Accepts, node_85, box_85, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_83 : Tree := .splitD (583 / 1536 : ℚ) node_84 node_85
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  change SplitDValid box_83 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_83], node_84_accepts, node_85_accepts⟩

private def box_79 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_79 : Tree := .splitC (179 / 512 : ℚ) node_80 node_83
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  change SplitCValid box_79 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_79], node_80_accepts, node_83_accepts⟩

private def box_71 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_71 : Tree := .splitD (97 / 256 : ℚ) node_72 node_79
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  change SplitDValid box_71 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_71], node_72_accepts, node_79_accepts⟩

private def box_89 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_89 : Tree := .leaf .projection
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_90 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_90 : Tree := .leaf .projection
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  norm_num [Tree.Accepts, node_90, box_90, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_88 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_88 : Tree := .splitD (581 / 1536 : ℚ) node_89 node_90
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  change SplitDValid box_88 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_88], node_89_accepts, node_90_accepts⟩

private def box_93 : Rectangle := ⟨(539 / 1536 : ℚ), (1079 / 3072 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_93 : Tree := .leaf .projection
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  norm_num [Tree.Accepts, node_93, box_93, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(1079 / 3072 : ℚ), (45 / 128 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_94 : Tree := .leaf .projection
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  norm_num [Tree.Accepts, node_94, box_94, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_92 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_92 : Tree := .splitC (1079 / 3072 : ℚ) node_93 node_94
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  change SplitCValid box_92 (1079 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_92], node_93_accepts, node_94_accepts⟩

private def box_95 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_95 : Tree := .leaf .projection
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  norm_num [Tree.Accepts, node_95, box_95, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_91 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_91 : Tree := .splitD (581 / 1536 : ℚ) node_92 node_95
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  change SplitDValid box_91 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_91], node_92_accepts, node_95_accepts⟩

private def box_87 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_87 : Tree := .splitC (539 / 1536 : ℚ) node_88 node_91
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  change SplitCValid box_87 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_87], node_88_accepts, node_91_accepts⟩

private def box_98 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_98 : Tree := .leaf .projection
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  norm_num [Tree.Accepts, node_98, box_98, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_99 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_99 : Tree := .leaf .projection
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  norm_num [Tree.Accepts, node_99, box_99, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_97 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_97 : Tree := .splitD (583 / 1536 : ℚ) node_98 node_99
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  change SplitDValid box_97 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_97], node_98_accepts, node_99_accepts⟩

private def box_101 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_101 : Tree := .leaf .projection
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  norm_num [Tree.Accepts, node_101, box_101, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_102 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_102 : Tree := .leaf .projection
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  norm_num [Tree.Accepts, node_102, box_102, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_100 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_100 : Tree := .splitD (583 / 1536 : ℚ) node_101 node_102
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  change SplitDValid box_100 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_100], node_101_accepts, node_102_accepts⟩

private def box_96 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_96 : Tree := .splitC (539 / 1536 : ℚ) node_97 node_100
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  change SplitCValid box_96 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_96], node_97_accepts, node_100_accepts⟩

private def box_86 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_86 : Tree := .splitD (97 / 256 : ℚ) node_87 node_96
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  change SplitDValid box_86 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_86], node_87_accepts, node_96_accepts⟩

private def box_70 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_70 : Tree := .splitC (269 / 768 : ℚ) node_71 node_86
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitCValid box_70 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_70], node_71_accepts, node_86_accepts⟩

private def box_0 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_0 : Tree := .splitD (145 / 384 : ℚ) node_1 node_70
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_70_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C030
