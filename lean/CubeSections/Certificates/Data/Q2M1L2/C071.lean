import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C071

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_8 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_7 : Tree := .splitD (161 / 384 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitDValid box_7 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_11 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_10 : Tree := .splitD (161 / 384 : ℚ) node_11 node_12
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitDValid box_10 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_10], node_11_accepts, node_12_accepts⟩

private def box_6 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_6 : Tree := .splitC (145 / 384 : ℚ) node_7 node_10
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitCValid box_6 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_6], node_7_accepts, node_10_accepts⟩

private def box_14 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_15 : Tree := .leaf .projection
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_13 : Tree := .splitC (145 / 384 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitCValid box_13 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_5 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_5 : Tree := .splitD (27 / 64 : ℚ) node_6 node_13
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_13_accepts⟩

private def box_19 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_18 : Tree := .splitD (161 / 384 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_22 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (5 / 12 : ℚ), (161 / 384 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (161 / 384 : ℚ), (27 / 64 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_21 : Tree := .splitD (161 / 384 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_17 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_17 : Tree := .splitC (49 / 128 : ℚ) node_18 node_21
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitCValid box_17 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_17], node_18_accepts, node_21_accepts⟩

private def box_25 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_24 : Tree := .splitC (49 / 128 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_16 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_16 : Tree := .splitD (27 / 64 : ℚ) node_17 node_24
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_24_accepts⟩

private def box_4 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_4 : Tree := .splitC (73 / 192 : ℚ) node_5 node_16
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_16_accepts⟩

private def box_29 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_28 : Tree := .splitD (83 / 192 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_32 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_31 : Tree := .splitD (83 / 192 : ℚ) node_32 node_33
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitDValid box_31 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_31], node_32_accepts, node_33_accepts⟩

private def box_27 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_27 : Tree := .splitC (73 / 192 : ℚ) node_28 node_31
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitCValid box_27 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_27], node_28_accepts, node_31_accepts⟩

private def box_3 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_3 : Tree := .splitD (41 / 96 : ℚ) node_4 node_27
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_27_accepts⟩

private def box_38 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(149 / 384 : ℚ), (25 / 64 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_37 : Tree := .splitC (149 / 384 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitCValid box_37 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_40 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_36 : Tree := .splitD (27 / 64 : ℚ) node_37 node_40
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitDValid box_36 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_36], node_37_accepts, node_40_accepts⟩

private def box_43 : Rectangle := ⟨(25 / 64 : ℚ), (151 / 384 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(151 / 384 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_42 : Tree := .splitC (151 / 384 : ℚ) node_43 node_44
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitCValid box_42 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_42], node_43_accepts, node_44_accepts⟩

private def box_45 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_41 : Tree := .splitD (27 / 64 : ℚ) node_42 node_45
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitDValid box_41 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_41], node_42_accepts, node_45_accepts⟩

private def box_35 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_35 : Tree := .splitC (25 / 64 : ℚ) node_36 node_41
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitCValid box_35 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_35], node_36_accepts, node_41_accepts⟩

private def box_48 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_47 : Tree := .splitD (83 / 192 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_51 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_51 : Tree := .leaf .projection
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_52 : Tree := .leaf .projection
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_50 : Tree := .splitD (83 / 192 : ℚ) node_51 node_52
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitDValid box_50 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_50], node_51_accepts, node_52_accepts⟩

private def box_46 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_46 : Tree := .splitC (25 / 64 : ℚ) node_47 node_50
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_50_accepts⟩

private def box_34 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_34 : Tree := .splitD (41 / 96 : ℚ) node_35 node_46
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_46_accepts⟩

private def box_2 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_2 : Tree := .splitC (37 / 96 : ℚ) node_3 node_34
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_34_accepts⟩

private def box_57 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (7 / 16 : ℚ), (85 / 192 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (85 / 192 : ℚ), (43 / 96 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_56 : Tree := .splitD (85 / 192 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitDValid box_56 (85 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_60 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (7 / 16 : ℚ), (85 / 192 : ℚ)⟩
private def node_60 : Tree := .leaf .projection
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (85 / 192 : ℚ), (43 / 96 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_59 : Tree := .splitD (85 / 192 : ℚ) node_60 node_61
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitDValid box_59 (85 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_59], node_60_accepts, node_61_accepts⟩

private def box_55 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_55 : Tree := .splitC (73 / 192 : ℚ) node_56 node_59
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitCValid box_55 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_55], node_56_accepts, node_59_accepts⟩

private def box_63 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_63 : Tree := .leaf .projection
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_64 : Tree := .leaf .projection
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  norm_num [Tree.Accepts, node_64, box_64, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_62 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_62 : Tree := .splitC (73 / 192 : ℚ) node_63 node_64
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitCValid box_62 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_62], node_63_accepts, node_64_accepts⟩

private def box_54 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_54 : Tree := .splitD (43 / 96 : ℚ) node_55 node_62
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitDValid box_54 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_54], node_55_accepts, node_62_accepts⟩

private def box_68 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (7 / 16 : ℚ), (85 / 192 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (85 / 192 : ℚ), (43 / 96 : ℚ)⟩
private def node_69 : Tree := .leaf .projection
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_67 : Tree := .splitD (85 / 192 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitDValid box_67 (85 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_71 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (7 / 16 : ℚ), (85 / 192 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (85 / 192 : ℚ), (43 / 96 : ℚ)⟩
private def node_72 : Tree := .leaf .projection
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_70 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_70 : Tree := .splitD (85 / 192 : ℚ) node_71 node_72
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitDValid box_70 (85 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_70], node_71_accepts, node_72_accepts⟩

private def box_66 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_66 : Tree := .splitC (25 / 64 : ℚ) node_67 node_70
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitCValid box_66 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_66], node_67_accepts, node_70_accepts⟩

private def box_74 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_74 : Tree := .leaf .projection
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  norm_num [Tree.Accepts, node_74, box_74, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_75 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_73 : Tree := .splitC (25 / 64 : ℚ) node_74 node_75
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitCValid box_73 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_73], node_74_accepts, node_75_accepts⟩

private def box_65 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_65 : Tree := .splitD (43 / 96 : ℚ) node_66 node_73
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitDValid box_65 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_65], node_66_accepts, node_73_accepts⟩

private def box_53 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_53 : Tree := .splitC (37 / 96 : ℚ) node_54 node_65
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitCValid box_53 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_53], node_54_accepts, node_65_accepts⟩

private def box_1 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_1 : Tree := .splitD (7 / 16 : ℚ) node_2 node_53
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_53_accepts⟩

private def box_81 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_81 : Tree := .leaf .projection
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  norm_num [Tree.Accepts, node_81, box_81, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_82 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_82 : Tree := .leaf .projection
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_80 : Tree := .splitD (27 / 64 : ℚ) node_81 node_82
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitDValid box_80 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_80], node_81_accepts, node_82_accepts⟩

private def box_84 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_84 : Tree := .leaf .projection
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  norm_num [Tree.Accepts, node_84, box_84, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_85 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_85 : Tree := .leaf .projection
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  norm_num [Tree.Accepts, node_85, box_85, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_83 : Tree := .splitD (27 / 64 : ℚ) node_84 node_85
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  change SplitDValid box_83 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_83], node_84_accepts, node_85_accepts⟩

private def box_79 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_79 : Tree := .splitC (77 / 192 : ℚ) node_80 node_83
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  change SplitCValid box_79 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_79], node_80_accepts, node_83_accepts⟩

private def box_88 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_88 : Tree := .leaf .projection
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  norm_num [Tree.Accepts, node_88, box_88, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_89 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_89 : Tree := .leaf .projection
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_87 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_87 : Tree := .splitD (83 / 192 : ℚ) node_88 node_89
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  change SplitDValid box_87 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_87], node_88_accepts, node_89_accepts⟩

private def box_91 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (41 / 96 : ℚ), (83 / 192 : ℚ)⟩
private def node_91 : Tree := .leaf .projection
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  norm_num [Tree.Accepts, node_91, box_91, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_92 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (83 / 192 : ℚ), (7 / 16 : ℚ)⟩
private def node_92 : Tree := .leaf .projection
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  norm_num [Tree.Accepts, node_92, box_92, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_90 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_90 : Tree := .splitD (83 / 192 : ℚ) node_91 node_92
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  change SplitDValid box_90 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_90], node_91_accepts, node_92_accepts⟩

private def box_86 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_86 : Tree := .splitC (77 / 192 : ℚ) node_87 node_90
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  change SplitCValid box_86 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_86], node_87_accepts, node_90_accepts⟩

private def box_78 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_78 : Tree := .splitD (41 / 96 : ℚ) node_79 node_86
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  change SplitDValid box_78 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_78], node_79_accepts, node_86_accepts⟩

private def box_96 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ), (27 / 64 : ℚ)⟩
private def node_96 : Tree := .leaf .projection
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  norm_num [Tree.Accepts, node_96, box_96, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_97 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (27 / 64 : ℚ), (41 / 96 : ℚ)⟩
private def node_97 : Tree := .leaf .projection
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  norm_num [Tree.Accepts, node_97, box_97, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_95 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_95 : Tree := .splitD (27 / 64 : ℚ) node_96 node_97
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  change SplitDValid box_95 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_95], node_96_accepts, node_97_accepts⟩

private def box_98 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_98 : Tree := .leaf .projection
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  norm_num [Tree.Accepts, node_98, box_98, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ)⟩
private def node_94 : Tree := .splitC (79 / 192 : ℚ) node_95 node_98
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  change SplitCValid box_94 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_94], node_95_accepts, node_98_accepts⟩

private def box_100 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_100 : Tree := .leaf .projection
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  norm_num [Tree.Accepts, node_100, box_100, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_101 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_101 : Tree := .leaf .projection
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  norm_num [Tree.Accepts, node_101, box_101, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_99 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (41 / 96 : ℚ), (7 / 16 : ℚ)⟩
private def node_99 : Tree := .splitC (79 / 192 : ℚ) node_100 node_101
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  change SplitCValid box_99 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_99], node_100_accepts, node_101_accepts⟩

private def box_93 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_93 : Tree := .splitD (41 / 96 : ℚ) node_94 node_99
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  change SplitDValid box_93 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_93], node_94_accepts, node_99_accepts⟩

private def box_77 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_77 : Tree := .splitC (13 / 32 : ℚ) node_78 node_93
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitCValid box_77 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_77], node_78_accepts, node_93_accepts⟩

private def box_105 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_105 : Tree := .leaf .projection
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  norm_num [Tree.Accepts, node_105, box_105, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_106 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_106 : Tree := .leaf .projection
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  norm_num [Tree.Accepts, node_106, box_106, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_104 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_104 : Tree := .splitC (77 / 192 : ℚ) node_105 node_106
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  change SplitCValid box_104 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_104], node_105_accepts, node_106_accepts⟩

private def box_107 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_107 : Tree := .leaf .projection
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  norm_num [Tree.Accepts, node_107, box_107, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_103 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_103 : Tree := .splitD (43 / 96 : ℚ) node_104 node_107
private theorem node_103_accepts : node_103.Accepts parameters box_103 := by
  change SplitDValid box_103 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_103], node_104_accepts, node_107_accepts⟩

private def box_109 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ), (43 / 96 : ℚ)⟩
private def node_109 : Tree := .leaf .projection
private theorem node_109_accepts : node_109.Accepts parameters box_109 := by
  norm_num [Tree.Accepts, node_109, box_109, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_110 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (43 / 96 : ℚ), (11 / 24 : ℚ)⟩
private def node_110 : Tree := .leaf .projection
private theorem node_110_accepts : node_110.Accepts parameters box_110 := by
  norm_num [Tree.Accepts, node_110, box_110, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_108 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_108 : Tree := .splitD (43 / 96 : ℚ) node_109 node_110
private theorem node_108_accepts : node_108.Accepts parameters box_108 := by
  change SplitDValid box_108 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_108], node_109_accepts, node_110_accepts⟩

private def box_102 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_102 : Tree := .splitC (13 / 32 : ℚ) node_103 node_108
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  change SplitCValid box_102 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_102], node_103_accepts, node_108_accepts⟩

private def box_76 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_76 : Tree := .splitD (7 / 16 : ℚ) node_77 node_102
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  change SplitDValid box_76 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_76], node_77_accepts, node_102_accepts⟩

private def box_0 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_0 : Tree := .splitC (19 / 48 : ℚ) node_1 node_76
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_76_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C071
