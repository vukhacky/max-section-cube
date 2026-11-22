import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C035

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_6 : Rectangle := ⟨(67 / 192 : ℚ), (179 / 512 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(179 / 512 : ℚ), (269 / 768 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_5 : Tree := .splitC (179 / 512 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (179 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_8 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_4 : Tree := .splitD (99 / 256 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (99 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_11 : Rectangle := ⟨(269 / 768 : ℚ), (539 / 1536 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(539 / 1536 : ℚ), (45 / 128 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_10 : Tree := .splitC (539 / 1536 : ℚ) node_11 node_12
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitCValid box_10 (539 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_10], node_11_accepts, node_12_accepts⟩

private def box_13 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_9 : Tree := .splitD (99 / 256 : ℚ) node_10 node_13
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitDValid box_9 (99 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_9], node_10_accepts, node_13_accepts⟩

private def box_3 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_3 : Tree := .splitC (269 / 768 : ℚ) node_4 node_9
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_9_accepts⟩

private def box_16 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (299 / 768 : ℚ), (25 / 64 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_15 : Tree := .splitD (299 / 768 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (299 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_19 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (299 / 768 : ℚ), (25 / 64 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_18 : Tree := .splitD (299 / 768 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (299 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_14 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_14 : Tree := .splitC (269 / 768 : ℚ) node_15 node_18
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitCValid box_14 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_14], node_15_accepts, node_18_accepts⟩

private def box_2 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_2 : Tree := .splitD (149 / 384 : ℚ) node_3 node_14
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_14_accepts⟩

private def box_25 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_24 : Tree := .splitC (541 / 1536 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (541 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_28 : Rectangle := ⟨(45 / 128 : ℚ), (541 / 1536 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(541 / 1536 : ℚ), (271 / 768 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_27 : Tree := .splitC (541 / 1536 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitCValid box_27 (541 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_23 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_23 : Tree := .splitD (99 / 256 : ℚ) node_24 node_27
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitDValid box_23 (99 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_23], node_24_accepts, node_27_accepts⟩

private def box_32 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (593 / 1536 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (593 / 1536 : ℚ), (99 / 256 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_33 : Tree := .splitD (593 / 1536 : ℚ) node_34 node_35
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (593 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_35_accepts⟩

private def box_31 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (99 / 256 : ℚ)⟩
private def node_31 : Tree := .splitC (181 / 512 : ℚ) node_32 node_33
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (181 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_33_accepts⟩

private def box_37 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_37 : Tree := .leaf .projection
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  norm_num [Tree.Accepts, node_37, box_37, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (99 / 256 : ℚ), (149 / 384 : ℚ)⟩
private def node_36 : Tree := .splitC (181 / 512 : ℚ) node_37 node_38
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitCValid box_36 (181 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_36], node_37_accepts, node_38_accepts⟩

private def box_30 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_30 : Tree := .splitD (99 / 256 : ℚ) node_31 node_36
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (99 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_36_accepts⟩

private def box_22 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_22 : Tree := .splitC (271 / 768 : ℚ) node_23 node_30
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitCValid box_22 (271 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_22], node_23_accepts, node_30_accepts⟩

private def box_41 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (299 / 768 : ℚ), (25 / 64 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_40 : Tree := .splitD (299 / 768 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (299 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_45 : Rectangle := ⟨(271 / 768 : ℚ), (181 / 512 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(181 / 512 : ℚ), (17 / 48 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (149 / 384 : ℚ), (299 / 768 : ℚ)⟩
private def node_44 : Tree := .splitC (181 / 512 : ℚ) node_45 node_46
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (181 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_46_accepts⟩

private def box_47 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (299 / 768 : ℚ), (25 / 64 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_43 : Tree := .splitD (299 / 768 : ℚ) node_44 node_47
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (299 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_47_accepts⟩

private def box_39 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_39 : Tree := .splitC (271 / 768 : ℚ) node_40 node_43
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitCValid box_39 (271 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_39], node_40_accepts, node_43_accepts⟩

private def box_21 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_21 : Tree := .splitD (149 / 384 : ℚ) node_22 node_39
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_39_accepts⟩

private def box_1 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_1 : Tree := .splitC (45 / 128 : ℚ) node_2 node_21
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_21_accepts⟩

private def box_52 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (25 / 64 : ℚ), (301 / 768 : ℚ)⟩
private def node_52 : Tree := .leaf .projection
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (301 / 768 : ℚ), (151 / 384 : ℚ)⟩
private def node_53 : Tree := .leaf .projection
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_51 : Tree := .splitD (301 / 768 : ℚ) node_52 node_53
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitDValid box_51 (301 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_51], node_52_accepts, node_53_accepts⟩

private def box_55 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (25 / 64 : ℚ), (301 / 768 : ℚ)⟩
private def node_55 : Tree := .leaf .projection
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (301 / 768 : ℚ), (151 / 384 : ℚ)⟩
private def node_56 : Tree := .leaf .projection
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_54 : Tree := .splitD (301 / 768 : ℚ) node_55 node_56
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitDValid box_54 (301 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_54], node_55_accepts, node_56_accepts⟩

private def box_50 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_50 : Tree := .splitC (269 / 768 : ℚ) node_51 node_54
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitCValid box_50 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_50], node_51_accepts, node_54_accepts⟩

private def box_59 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (151 / 384 : ℚ), (101 / 256 : ℚ)⟩
private def node_59 : Tree := .leaf .projection
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (101 / 256 : ℚ), (19 / 48 : ℚ)⟩
private def node_60 : Tree := .leaf .projection
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_58 : Tree := .splitD (101 / 256 : ℚ) node_59 node_60
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  change SplitDValid box_58 (101 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_58], node_59_accepts, node_60_accepts⟩

private def box_62 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (151 / 384 : ℚ), (101 / 256 : ℚ)⟩
private def node_62 : Tree := .leaf .projection
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (101 / 256 : ℚ), (19 / 48 : ℚ)⟩
private def node_63 : Tree := .leaf .projection
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_61 : Tree := .splitD (101 / 256 : ℚ) node_62 node_63
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitDValid box_61 (101 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_61], node_62_accepts, node_63_accepts⟩

private def box_57 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_57 : Tree := .splitC (269 / 768 : ℚ) node_58 node_61
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitCValid box_57 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_57], node_58_accepts, node_61_accepts⟩

private def box_49 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_49 : Tree := .splitD (151 / 384 : ℚ) node_50 node_57
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitDValid box_49 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_49], node_50_accepts, node_57_accepts⟩

private def box_67 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (25 / 64 : ℚ), (301 / 768 : ℚ)⟩
private def node_67 : Tree := .leaf .projection
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_68 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (301 / 768 : ℚ), (151 / 384 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_66 : Tree := .splitD (301 / 768 : ℚ) node_67 node_68
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitDValid box_66 (301 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_66], node_67_accepts, node_68_accepts⟩

private def box_70 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (25 / 64 : ℚ), (301 / 768 : ℚ)⟩
private def node_70 : Tree := .leaf .projection
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  norm_num [Tree.Accepts, node_70, box_70, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (301 / 768 : ℚ), (151 / 384 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_69 : Tree := .splitD (301 / 768 : ℚ) node_70 node_71
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  change SplitDValid box_69 (301 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_69], node_70_accepts, node_71_accepts⟩

private def box_65 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_65 : Tree := .splitC (271 / 768 : ℚ) node_66 node_69
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitCValid box_65 (271 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_65], node_66_accepts, node_69_accepts⟩

private def box_74 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (151 / 384 : ℚ), (101 / 256 : ℚ)⟩
private def node_74 : Tree := .leaf .projection
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  norm_num [Tree.Accepts, node_74, box_74, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_75 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (101 / 256 : ℚ), (19 / 48 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_73 : Tree := .splitD (101 / 256 : ℚ) node_74 node_75
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitDValid box_73 (101 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_73], node_74_accepts, node_75_accepts⟩

private def box_77 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (151 / 384 : ℚ), (101 / 256 : ℚ)⟩
private def node_77 : Tree := .leaf .projection
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  norm_num [Tree.Accepts, node_77, box_77, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (101 / 256 : ℚ), (19 / 48 : ℚ)⟩
private def node_78 : Tree := .leaf .projection
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_76 : Tree := .splitD (101 / 256 : ℚ) node_77 node_78
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  change SplitDValid box_76 (101 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_76], node_77_accepts, node_78_accepts⟩

private def box_72 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_72 : Tree := .splitC (271 / 768 : ℚ) node_73 node_76
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitCValid box_72 (271 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_72], node_73_accepts, node_76_accepts⟩

private def box_64 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_64 : Tree := .splitD (151 / 384 : ℚ) node_65 node_72
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitDValid box_64 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_64], node_65_accepts, node_72_accepts⟩

private def box_48 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_48 : Tree := .splitC (45 / 128 : ℚ) node_49 node_64
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitCValid box_48 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_48], node_49_accepts, node_64_accepts⟩

private def box_0 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_0 : Tree := .splitD (25 / 64 : ℚ) node_1 node_48
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_48_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C035
