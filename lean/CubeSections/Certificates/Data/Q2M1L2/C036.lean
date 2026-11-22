import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C036

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_5 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_5 : Tree := .leaf .projection
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_6 : Tree := .splitD (51 / 128 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_4 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_4 : Tree := .splitC (43 / 128 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (43 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_10 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_9 : Tree := .splitC (43 / 128 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (43 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_3 : Tree := .splitD (77 / 192 : ℚ) node_4 node_9
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_9_accepts⟩

private def box_15 : Rectangle := ⟨(65 / 192 : ℚ), (131 / 384 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_15 : Tree := .leaf .projection
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(65 / 192 : ℚ), (131 / 384 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(65 / 192 : ℚ), (131 / 384 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_14 : Tree := .splitD (51 / 128 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitDValid box_14 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_18 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_17 : Tree := .splitD (51 / 128 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitDValid box_17 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_13 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_13 : Tree := .splitC (131 / 384 : ℚ) node_14 node_17
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitCValid box_13 (131 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_13], node_14_accepts, node_17_accepts⟩

private def box_21 : Rectangle := ⟨(65 / 192 : ℚ), (131 / 384 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_24 : Tree := .leaf .projection
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_22 : Tree := .splitD (155 / 384 : ℚ) node_23 node_24
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitDValid box_22 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_22], node_23_accepts, node_24_accepts⟩

private def box_20 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_20 : Tree := .splitC (131 / 384 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (131 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_12 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_12 : Tree := .splitD (77 / 192 : ℚ) node_13 node_20
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_20_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_2 : Tree := .splitC (65 / 192 : ℚ) node_3 node_12
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (65 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_12_accepts⟩

private def box_27 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_26 : Tree := .splitD (79 / 192 : ℚ) node_27 node_28
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitDValid box_26 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_26], node_27_accepts, node_28_accepts⟩

private def box_31 : Rectangle := ⟨(65 / 192 : ℚ), (131 / 384 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(131 / 384 : ℚ), (11 / 32 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_30 : Tree := .splitC (131 / 384 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitCValid box_30 (131 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_33 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_29 : Tree := .splitD (79 / 192 : ℚ) node_30 node_33
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitDValid box_29 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_29], node_30_accepts, node_33_accepts⟩

private def box_25 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_25 : Tree := .splitC (65 / 192 : ℚ) node_26 node_29
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitCValid box_25 (65 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_25], node_26_accepts, node_29_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_1 : Tree := .splitD (13 / 32 : ℚ) node_2 node_25
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_25_accepts⟩

private def box_39 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_38 : Tree := .splitD (51 / 128 : ℚ) node_39 node_40
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitDValid box_38 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_38], node_39_accepts, node_40_accepts⟩

private def box_43 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_42 : Tree := .splitC (89 / 256 : ℚ) node_43 node_44
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitCValid box_42 (89 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_42], node_43_accepts, node_44_accepts⟩

private def box_45 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_41 : Tree := .splitD (51 / 128 : ℚ) node_42 node_45
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitDValid box_41 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_41], node_42_accepts, node_45_accepts⟩

private def box_37 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_37 : Tree := .splitC (133 / 384 : ℚ) node_38 node_41
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitCValid box_37 (133 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_37], node_38_accepts, node_41_accepts⟩

private def box_48 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_47 : Tree := .splitD (155 / 384 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_51 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_51 : Tree := .leaf .projection
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_52 : Tree := .leaf .projection
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_50 : Tree := .splitD (155 / 384 : ℚ) node_51 node_52
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitDValid box_50 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_50], node_51_accepts, node_52_accepts⟩

private def box_46 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_46 : Tree := .splitC (133 / 384 : ℚ) node_47 node_50
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (133 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_50_accepts⟩

private def box_36 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_36 : Tree := .splitD (77 / 192 : ℚ) node_37 node_46
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitDValid box_36 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_36], node_37_accepts, node_46_accepts⟩

private def box_57 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_56 : Tree := .splitC (269 / 768 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitCValid box_56 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_60 : Rectangle := ⟨(67 / 192 : ℚ), (269 / 768 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_60 : Tree := .leaf .projection
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(269 / 768 : ℚ), (45 / 128 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_59 : Tree := .splitC (269 / 768 : ℚ) node_60 node_61
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitCValid box_59 (269 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_59], node_60_accepts, node_61_accepts⟩

private def box_55 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_55 : Tree := .splitD (51 / 128 : ℚ) node_56 node_59
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitDValid box_55 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_55], node_56_accepts, node_59_accepts⟩

private def box_65 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (19 / 48 : ℚ), (305 / 768 : ℚ)⟩
private def node_65 : Tree := .leaf .projection
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (305 / 768 : ℚ), (51 / 128 : ℚ)⟩
private def node_66 : Tree := .leaf .projection
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_64 : Tree := .splitD (305 / 768 : ℚ) node_65 node_66
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitDValid box_64 (305 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_64], node_65_accepts, node_66_accepts⟩

private def box_68 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (305 / 768 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (305 / 768 : ℚ), (51 / 128 : ℚ)⟩
private def node_69 : Tree := .leaf .projection
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_67 : Tree := .splitD (305 / 768 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitDValid box_67 (305 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_63 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_63 : Tree := .splitC (271 / 768 : ℚ) node_64 node_67
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitCValid box_63 (271 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_63], node_64_accepts, node_67_accepts⟩

private def box_71 : Rectangle := ⟨(45 / 128 : ℚ), (271 / 768 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(271 / 768 : ℚ), (17 / 48 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_72 : Tree := .leaf .projection
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_70 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_70 : Tree := .splitC (271 / 768 : ℚ) node_71 node_72
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitCValid box_70 (271 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_70], node_71_accepts, node_72_accepts⟩

private def box_62 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_62 : Tree := .splitD (51 / 128 : ℚ) node_63 node_70
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitDValid box_62 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_62], node_63_accepts, node_70_accepts⟩

private def box_54 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_54 : Tree := .splitC (45 / 128 : ℚ) node_55 node_62
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitCValid box_54 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_54], node_55_accepts, node_62_accepts⟩

private def box_75 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_76 : Tree := .leaf .projection
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_74 : Tree := .splitD (155 / 384 : ℚ) node_75 node_76
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitDValid box_74 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_74], node_75_accepts, node_76_accepts⟩

private def box_78 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_78 : Tree := .leaf .projection
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_79 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_79 : Tree := .leaf .projection
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_77 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_77 : Tree := .splitD (155 / 384 : ℚ) node_78 node_79
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitDValid box_77 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_77], node_78_accepts, node_79_accepts⟩

private def box_73 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_73 : Tree := .splitC (45 / 128 : ℚ) node_74 node_77
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitCValid box_73 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_73], node_74_accepts, node_77_accepts⟩

private def box_53 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_53 : Tree := .splitD (77 / 192 : ℚ) node_54 node_73
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitDValid box_53 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_53], node_54_accepts, node_73_accepts⟩

private def box_35 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_35 : Tree := .splitC (67 / 192 : ℚ) node_36 node_53
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitCValid box_35 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_35], node_36_accepts, node_53_accepts⟩

private def box_83 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_83 : Tree := .leaf .projection
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_85 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (13 / 32 : ℚ), (157 / 384 : ℚ)⟩
private def node_85 : Tree := .leaf .projection
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  norm_num [Tree.Accepts, node_85, box_85, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_86 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (157 / 384 : ℚ), (79 / 192 : ℚ)⟩
private def node_86 : Tree := .leaf .projection
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  norm_num [Tree.Accepts, node_86, box_86, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_84 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_84 : Tree := .splitD (157 / 384 : ℚ) node_85 node_86
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  change SplitDValid box_84 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_84], node_85_accepts, node_86_accepts⟩

private def box_82 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_82 : Tree := .splitC (133 / 384 : ℚ) node_83 node_84
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  change SplitCValid box_82 (133 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_82], node_83_accepts, node_84_accepts⟩

private def box_88 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_88 : Tree := .leaf .projection
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  norm_num [Tree.Accepts, node_88, box_88, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_89 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_89 : Tree := .leaf .projection
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_87 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_87 : Tree := .splitC (133 / 384 : ℚ) node_88 node_89
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  change SplitCValid box_87 (133 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_87], node_88_accepts, node_89_accepts⟩

private def box_81 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_81 : Tree := .splitD (79 / 192 : ℚ) node_82 node_87
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitDValid box_81 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_81], node_82_accepts, node_87_accepts⟩

private def box_93 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (13 / 32 : ℚ), (157 / 384 : ℚ)⟩
private def node_93 : Tree := .leaf .projection
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  norm_num [Tree.Accepts, node_93, box_93, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (157 / 384 : ℚ), (79 / 192 : ℚ)⟩
private def node_94 : Tree := .leaf .projection
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  norm_num [Tree.Accepts, node_94, box_94, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_92 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_92 : Tree := .splitD (157 / 384 : ℚ) node_93 node_94
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  change SplitDValid box_92 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_92], node_93_accepts, node_94_accepts⟩

private def box_96 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (13 / 32 : ℚ), (157 / 384 : ℚ)⟩
private def node_96 : Tree := .leaf .projection
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  norm_num [Tree.Accepts, node_96, box_96, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_97 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (157 / 384 : ℚ), (79 / 192 : ℚ)⟩
private def node_97 : Tree := .leaf .projection
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  norm_num [Tree.Accepts, node_97, box_97, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_95 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_95 : Tree := .splitD (157 / 384 : ℚ) node_96 node_97
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  change SplitDValid box_95 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_95], node_96_accepts, node_97_accepts⟩

private def box_91 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_91 : Tree := .splitC (45 / 128 : ℚ) node_92 node_95
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  change SplitCValid box_91 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_91], node_92_accepts, node_95_accepts⟩

private def box_99 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_99 : Tree := .leaf .projection
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  norm_num [Tree.Accepts, node_99, box_99, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_101 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (79 / 192 : ℚ), (53 / 128 : ℚ)⟩
private def node_101 : Tree := .leaf .projection
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  norm_num [Tree.Accepts, node_101, box_101, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_102 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (53 / 128 : ℚ), (5 / 12 : ℚ)⟩
private def node_102 : Tree := .leaf .projection
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  norm_num [Tree.Accepts, node_102, box_102, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_100 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_100 : Tree := .splitD (53 / 128 : ℚ) node_101 node_102
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  change SplitDValid box_100 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_100], node_101_accepts, node_102_accepts⟩

private def box_98 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_98 : Tree := .splitC (45 / 128 : ℚ) node_99 node_100
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  change SplitCValid box_98 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_98], node_99_accepts, node_100_accepts⟩

private def box_90 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_90 : Tree := .splitD (79 / 192 : ℚ) node_91 node_98
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  change SplitDValid box_90 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_90], node_91_accepts, node_98_accepts⟩

private def box_80 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_80 : Tree := .splitC (67 / 192 : ℚ) node_81 node_90
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitCValid box_80 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_80], node_81_accepts, node_90_accepts⟩

private def box_34 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_34 : Tree := .splitD (13 / 32 : ℚ) node_35 node_80
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_80_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_0 : Tree := .splitC (11 / 32 : ℚ) node_1 node_34
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_34_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C036
