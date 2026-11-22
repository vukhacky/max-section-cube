import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C024

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_4 : Rectangle := ⟨(1 / 3 : ℚ), (257 / 768 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (329 / 1024 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(257 / 768 : ℚ), (43 / 128 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (83 / 256 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_3 : Tree := .splitC (257 / 768 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (257 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_8 : Rectangle := ⟨(1 / 3 : ℚ), (257 / 768 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(1 / 3 : ℚ), (257 / 768 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(1 / 3 : ℚ), (257 / 768 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_7 : Tree := .splitD (97 / 256 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitDValid box_7 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_11 : Rectangle := ⟨(257 / 768 : ℚ), (43 / 128 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(257 / 768 : ℚ), (43 / 128 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(257 / 768 : ℚ), (43 / 128 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_10 : Tree := .splitD (97 / 256 : ℚ) node_11 node_12
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitDValid box_10 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_10], node_11_accepts, node_12_accepts⟩

private def box_6 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_6 : Tree := .splitC (257 / 768 : ℚ) node_7 node_10
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitCValid box_6 (257 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_6], node_7_accepts, node_10_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_2 : Tree := .splitD (145 / 384 : ℚ) node_3 node_6
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_6_accepts⟩

private def box_16 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_15 : Tree := .splitD (289 / 768 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_19 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (3 / 8 : ℚ), (289 / 768 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (289 / 768 : ℚ), (145 / 384 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_18 : Tree := .splitD (289 / 768 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_14 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_14 : Tree := .splitC (259 / 768 : ℚ) node_15 node_18
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitCValid box_14 (259 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_14], node_15_accepts, node_18_accepts⟩

private def box_23 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_24 : Tree := .leaf .projection
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_22 : Tree := .splitD (97 / 256 : ℚ) node_23 node_24
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitDValid box_22 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_22], node_23_accepts, node_24_accepts⟩

private def box_26 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (145 / 384 : ℚ), (97 / 256 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (97 / 256 : ℚ), (73 / 192 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_25 : Tree := .splitD (97 / 256 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitDValid box_25 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_21 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_21 : Tree := .splitC (259 / 768 : ℚ) node_22 node_25
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitCValid box_21 (259 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_21], node_22_accepts, node_25_accepts⟩

private def box_13 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_13 : Tree := .splitD (145 / 384 : ℚ) node_14 node_21
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_21_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_1 : Tree := .splitC (43 / 128 : ℚ) node_2 node_13
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (43 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_13_accepts⟩

private def box_31 : Rectangle := ⟨(1 / 3 : ℚ), (257 / 768 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(257 / 768 : ℚ), (43 / 128 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(257 / 768 : ℚ), (43 / 128 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(257 / 768 : ℚ), (43 / 128 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_32 : Tree := .splitD (293 / 768 : ℚ) node_33 node_34
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitDValid box_32 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_32], node_33_accepts, node_34_accepts⟩

private def box_30 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_30 : Tree := .splitC (257 / 768 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitCValid box_30 (257 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_36 : Rectangle := ⟨(1 / 3 : ℚ), (257 / 768 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(257 / 768 : ℚ), (43 / 128 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_37 : Tree := .leaf .projection
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  norm_num [Tree.Accepts, node_37, box_37, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_35 : Tree := .splitC (257 / 768 : ℚ) node_36 node_37
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitCValid box_35 (257 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_35], node_36_accepts, node_37_accepts⟩

private def box_29 : Rectangle := ⟨(1 / 3 : ℚ), (43 / 128 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_29 : Tree := .splitD (49 / 128 : ℚ) node_30 node_35
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitDValid box_29 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_29], node_30_accepts, node_35_accepts⟩

private def box_41 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_40 : Tree := .splitD (293 / 768 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_44 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (73 / 192 : ℚ), (293 / 768 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (293 / 768 : ℚ), (49 / 128 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_43 : Tree := .splitD (293 / 768 : ℚ) node_44 node_45
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_45_accepts⟩

private def box_39 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_39 : Tree := .splitC (259 / 768 : ℚ) node_40 node_43
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitCValid box_39 (259 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_39], node_40_accepts, node_43_accepts⟩

private def box_47 : Rectangle := ⟨(43 / 128 : ℚ), (259 / 768 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (49 / 128 : ℚ), (295 / 768 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (295 / 768 : ℚ), (37 / 96 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(259 / 768 : ℚ), (65 / 192 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_48 : Tree := .splitD (295 / 768 : ℚ) node_49 node_50
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitDValid box_48 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_48], node_49_accepts, node_50_accepts⟩

private def box_46 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_46 : Tree := .splitC (259 / 768 : ℚ) node_47 node_48
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (259 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_48_accepts⟩

private def box_38 : Rectangle := ⟨(43 / 128 : ℚ), (65 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_38 : Tree := .splitD (49 / 128 : ℚ) node_39 node_46
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitDValid box_38 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_38], node_39_accepts, node_46_accepts⟩

private def box_28 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_28 : Tree := .splitC (43 / 128 : ℚ) node_29 node_38
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitCValid box_28 (43 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_28], node_29_accepts, node_38_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_0 : Tree := .splitD (73 / 192 : ℚ) node_1 node_28
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_28_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C024
