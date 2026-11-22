import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C069

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_7 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_6 : Tree := .splitD (145 / 384 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_9 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_5 : Tree := .splitC (51 / 128 : ℚ) node_6 node_9
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_9_accepts⟩

private def box_12 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_11 : Tree := .splitD (49 / 128 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_14 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_10 : Tree := .splitC (51 / 128 : ℚ) node_11 node_14
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitCValid box_10 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_10], node_11_accepts, node_14_accepts⟩

private def box_4 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_4 : Tree := .splitD (73 / 192 : ℚ) node_5 node_10
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_10_accepts⟩

private def box_16 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_15 : Tree := .splitD (73 / 192 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_3 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_3 : Tree := .splitC (77 / 192 : ℚ) node_4 node_15
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_15_accepts⟩

private def box_22 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_21 : Tree := .splitD (149 / 384 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_24 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_24 : Tree := .leaf .projection
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_20 : Tree := .splitC (51 / 128 : ℚ) node_21 node_24
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_24_accepts⟩

private def box_27 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_26 : Tree := .splitD (151 / 384 : ℚ) node_27 node_28
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitDValid box_26 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_26], node_27_accepts, node_28_accepts⟩

private def box_29 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_25 : Tree := .splitC (51 / 128 : ℚ) node_26 node_29
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitCValid box_25 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_25], node_26_accepts, node_29_accepts⟩

private def box_19 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_19 : Tree := .splitD (25 / 64 : ℚ) node_20 node_25
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_25_accepts⟩

private def box_31 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_30 : Tree := .splitD (25 / 64 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_18 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_18 : Tree := .splitC (77 / 192 : ℚ) node_19 node_30
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitCValid box_18 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_18], node_19_accepts, node_30_accepts⟩

private def box_2 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_2 : Tree := .splitD (37 / 96 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_36 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_37 : Tree := .leaf .projection
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  norm_num [Tree.Accepts, node_37, box_37, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_35 : Tree := .splitD (73 / 192 : ℚ) node_36 node_37
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitDValid box_35 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_35], node_36_accepts, node_37_accepts⟩

private def box_39 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_38 : Tree := .splitD (73 / 192 : ℚ) node_39 node_40
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitDValid box_38 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_38], node_39_accepts, node_40_accepts⟩

private def box_34 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_34 : Tree := .splitC (79 / 192 : ℚ) node_35 node_38
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitCValid box_34 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_34], node_35_accepts, node_38_accepts⟩

private def box_43 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_42 : Tree := .splitD (25 / 64 : ℚ) node_43 node_44
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitDValid box_42 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_42], node_43_accepts, node_44_accepts⟩

private def box_46 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_45 : Tree := .splitD (25 / 64 : ℚ) node_46 node_47
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitDValid box_45 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_45], node_46_accepts, node_47_accepts⟩

private def box_41 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_41 : Tree := .splitC (79 / 192 : ℚ) node_42 node_45
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitCValid box_41 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_41], node_42_accepts, node_45_accepts⟩

private def box_33 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_33 : Tree := .splitD (37 / 96 : ℚ) node_34 node_41
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_41_accepts⟩

private def box_1 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_1 : Tree := .splitC (13 / 32 : ℚ) node_2 node_33
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_33_accepts⟩

private def box_54 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_55 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_55 : Tree := .leaf .projection
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_53 : Tree := .splitD (51 / 128 : ℚ) node_54 node_55
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitDValid box_53 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_53], node_54_accepts, node_55_accepts⟩

private def box_56 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_56 : Tree := .leaf .projection
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_52 : Tree := .splitC (51 / 128 : ℚ) node_53 node_56
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitCValid box_52 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_52], node_53_accepts, node_56_accepts⟩

private def box_58 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_59 : Tree := .leaf .projection
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_57 : Tree := .splitC (51 / 128 : ℚ) node_58 node_59
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitCValid box_57 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_57], node_58_accepts, node_59_accepts⟩

private def box_51 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_51 : Tree := .splitD (77 / 192 : ℚ) node_52 node_57
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitDValid box_51 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_51], node_52_accepts, node_57_accepts⟩

private def box_61 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_62 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_62 : Tree := .leaf .projection
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_60 : Tree := .splitD (77 / 192 : ℚ) node_61 node_62
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitDValid box_60 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_60], node_61_accepts, node_62_accepts⟩

private def box_50 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_50 : Tree := .splitC (77 / 192 : ℚ) node_51 node_60
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitCValid box_50 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_50], node_51_accepts, node_60_accepts⟩

private def box_66 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_66 : Tree := .leaf .projection
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_67 : Tree := .leaf .projection
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_65 : Tree := .splitC (51 / 128 : ℚ) node_66 node_67
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitCValid box_65 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_65], node_66_accepts, node_67_accepts⟩

private def box_68 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_64 : Tree := .splitD (79 / 192 : ℚ) node_65 node_68
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitDValid box_64 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_64], node_65_accepts, node_68_accepts⟩

private def box_70 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_70 : Tree := .leaf .projection
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  norm_num [Tree.Accepts, node_70, box_70, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_69 : Tree := .splitD (79 / 192 : ℚ) node_70 node_71
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  change SplitDValid box_69 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_69], node_70_accepts, node_71_accepts⟩

private def box_63 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_63 : Tree := .splitC (77 / 192 : ℚ) node_64 node_69
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitCValid box_63 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_63], node_64_accepts, node_69_accepts⟩

private def box_49 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_49 : Tree := .splitD (13 / 32 : ℚ) node_50 node_63
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitDValid box_49 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_49], node_50_accepts, node_63_accepts⟩

private def box_75 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_76 : Tree := .leaf .projection
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_74 : Tree := .splitD (77 / 192 : ℚ) node_75 node_76
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitDValid box_74 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_74], node_75_accepts, node_76_accepts⟩

private def box_78 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_78 : Tree := .leaf .projection
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_79 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_79 : Tree := .leaf .projection
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_77 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_77 : Tree := .splitD (77 / 192 : ℚ) node_78 node_79
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitDValid box_77 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_77], node_78_accepts, node_79_accepts⟩

private def box_73 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_73 : Tree := .splitC (79 / 192 : ℚ) node_74 node_77
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitCValid box_73 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_73], node_74_accepts, node_77_accepts⟩

private def box_82 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_82 : Tree := .leaf .projection
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_83 : Tree := .leaf .projection
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_81 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_81 : Tree := .splitD (79 / 192 : ℚ) node_82 node_83
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitDValid box_81 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_81], node_82_accepts, node_83_accepts⟩

private def box_85 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_85 : Tree := .leaf .projection
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  norm_num [Tree.Accepts, node_85, box_85, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_86 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_86 : Tree := .leaf .projection
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  norm_num [Tree.Accepts, node_86, box_86, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_84 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_84 : Tree := .splitD (79 / 192 : ℚ) node_85 node_86
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  change SplitDValid box_84 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_84], node_85_accepts, node_86_accepts⟩

private def box_80 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_80 : Tree := .splitC (79 / 192 : ℚ) node_81 node_84
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitCValid box_80 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_80], node_81_accepts, node_84_accepts⟩

private def box_72 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_72 : Tree := .splitD (13 / 32 : ℚ) node_73 node_80
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitDValid box_72 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_72], node_73_accepts, node_80_accepts⟩

private def box_48 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_48 : Tree := .splitC (13 / 32 : ℚ) node_49 node_72
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitCValid box_48 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_48], node_49_accepts, node_72_accepts⟩

private def box_0 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_0 : Tree := .splitD (19 / 48 : ℚ) node_1 node_48
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_48_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C069
