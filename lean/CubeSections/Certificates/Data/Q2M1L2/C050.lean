import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C050

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_6 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_5 : Tree := .splitC (1121 / 3072 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_9 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_8 : Tree := .splitC (1121 / 3072 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitCValid box_8 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_4 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_4 : Tree := .splitD (577 / 1536 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_13 : Rectangle := ⟨(187 / 512 : ℚ), (1123 / 3072 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(1123 / 3072 : ℚ), (281 / 768 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_12 : Tree := .splitC (1123 / 3072 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (1123 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_16 : Rectangle := ⟨(187 / 512 : ℚ), (1123 / 3072 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(1123 / 3072 : ℚ), (281 / 768 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_15 : Tree := .splitC (1123 / 3072 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (1123 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_11 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_11 : Tree := .splitD (577 / 1536 : ℚ) node_12 node_15
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_15_accepts⟩

private def box_3 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_3 : Tree := .splitC (187 / 512 : ℚ) node_4 node_11
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (187 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_11_accepts⟩

private def box_21 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_20 : Tree := .splitC (1121 / 3072 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_24 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_24 : Tree := .leaf .projection
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_23 : Tree := .splitC (1121 / 3072 : ℚ) node_24 node_25
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitCValid box_23 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_23], node_24_accepts, node_25_accepts⟩

private def box_19 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_19 : Tree := .splitD (193 / 512 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_28 : Rectangle := ⟨(187 / 512 : ℚ), (1123 / 3072 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(1123 / 3072 : ℚ), (281 / 768 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_27 : Tree := .splitC (1123 / 3072 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitCValid box_27 (1123 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_30 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_26 : Tree := .splitD (193 / 512 : ℚ) node_27 node_30
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitDValid box_26 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_26], node_27_accepts, node_30_accepts⟩

private def box_18 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_18 : Tree := .splitC (187 / 512 : ℚ) node_19 node_26
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitCValid box_18 (187 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_18], node_19_accepts, node_26_accepts⟩

private def box_2 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_2 : Tree := .splitD (289 / 768 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_34 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_33 : Tree := .splitD (577 / 1536 : ℚ) node_34 node_35
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_35_accepts⟩

private def box_37 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (3 / 8 : ℚ), (577 / 1536 : ℚ)⟩
private def node_37 : Tree := .leaf .projection
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  norm_num [Tree.Accepts, node_37, box_37, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (577 / 1536 : ℚ), (289 / 768 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_36 : Tree := .splitD (577 / 1536 : ℚ) node_37 node_38
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitDValid box_36 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_36], node_37_accepts, node_38_accepts⟩

private def box_32 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_32 : Tree := .splitC (563 / 1536 : ℚ) node_33 node_36
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitCValid box_32 (563 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_32], node_33_accepts, node_36_accepts⟩

private def box_41 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_40 : Tree := .splitD (193 / 512 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_44 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (289 / 768 : ℚ), (193 / 512 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (193 / 512 : ℚ), (145 / 384 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_43 : Tree := .splitD (193 / 512 : ℚ) node_44 node_45
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (193 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_45_accepts⟩

private def box_39 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_39 : Tree := .splitC (563 / 1536 : ℚ) node_40 node_43
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitCValid box_39 (563 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_39], node_40_accepts, node_43_accepts⟩

private def box_31 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_31 : Tree := .splitD (289 / 768 : ℚ) node_32 node_39
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitDValid box_31 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_31], node_32_accepts, node_39_accepts⟩

private def box_1 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_1 : Tree := .splitC (281 / 768 : ℚ) node_2 node_31
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (281 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_31_accepts⟩

private def box_50 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_51 : Tree := .leaf .projection
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_49 : Tree := .splitD (581 / 1536 : ℚ) node_50 node_51
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitDValid box_49 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_49], node_50_accepts, node_51_accepts⟩

private def box_53 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_53 : Tree := .leaf .projection
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_52 : Tree := .splitD (581 / 1536 : ℚ) node_53 node_54
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitDValid box_52 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_52], node_53_accepts, node_54_accepts⟩

private def box_48 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_48 : Tree := .splitC (187 / 512 : ℚ) node_49 node_52
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitCValid box_48 (187 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_48], node_49_accepts, node_52_accepts⟩

private def box_57 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_56 : Tree := .splitD (583 / 1536 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitDValid box_56 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_60 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_60 : Tree := .leaf .projection
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_59 : Tree := .splitD (583 / 1536 : ℚ) node_60 node_61
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitDValid box_59 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_59], node_60_accepts, node_61_accepts⟩

private def box_55 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_55 : Tree := .splitC (187 / 512 : ℚ) node_56 node_59
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitCValid box_55 (187 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_55], node_56_accepts, node_59_accepts⟩

private def box_47 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_47 : Tree := .splitD (97 / 256 : ℚ) node_48 node_55
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_55_accepts⟩

private def box_65 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_65 : Tree := .leaf .projection
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_66 : Tree := .leaf .projection
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_64 : Tree := .splitD (581 / 1536 : ℚ) node_65 node_66
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitDValid box_64 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_64], node_65_accepts, node_66_accepts⟩

private def box_68 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (145 / 384 : ℚ), (581 / 1536 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (581 / 1536 : ℚ), (97 / 256 : ℚ)⟩
private def node_69 : Tree := .leaf .projection
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_67 : Tree := .splitD (581 / 1536 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitDValid box_67 (581 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_63 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_63 : Tree := .splitC (563 / 1536 : ℚ) node_64 node_67
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitCValid box_63 (563 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_63], node_64_accepts, node_67_accepts⟩

private def box_72 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_72 : Tree := .leaf .projection
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_73 : Tree := .leaf .projection
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  norm_num [Tree.Accepts, node_73, box_73, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_71 : Tree := .splitD (583 / 1536 : ℚ) node_72 node_73
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  change SplitDValid box_71 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_71], node_72_accepts, node_73_accepts⟩

private def box_75 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (97 / 256 : ℚ), (583 / 1536 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (583 / 1536 : ℚ), (73 / 192 : ℚ)⟩
private def node_76 : Tree := .leaf .projection
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_74 : Tree := .splitD (583 / 1536 : ℚ) node_75 node_76
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitDValid box_74 (583 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_74], node_75_accepts, node_76_accepts⟩

private def box_70 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_70 : Tree := .splitC (563 / 1536 : ℚ) node_71 node_74
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitCValid box_70 (563 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_70], node_71_accepts, node_74_accepts⟩

private def box_62 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_62 : Tree := .splitD (97 / 256 : ℚ) node_63 node_70
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitDValid box_62 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_62], node_63_accepts, node_70_accepts⟩

private def box_46 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_46 : Tree := .splitC (281 / 768 : ℚ) node_47 node_62
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (281 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_62_accepts⟩

private def box_0 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_0 : Tree := .splitD (145 / 384 : ℚ) node_1 node_46
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_46_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C050
