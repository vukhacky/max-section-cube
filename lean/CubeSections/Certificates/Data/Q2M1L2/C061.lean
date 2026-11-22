import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C061

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_3 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (17 / 48 : ℚ), (23 / 64 : ℚ)⟩
private def node_3 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  norm_num [Tree.Accepts, node_3, box_3, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (89 / 256 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_2 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_2 : Tree := .splitD (23 / 64 : ℚ) node_3 node_4
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_4_accepts⟩

private def box_6 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (17 / 48 : ℚ), (23 / 64 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (89 / 256 : ℚ))
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ)⟩
private def node_9 : Tree := .leaf (.strip (179 / 512 : ℚ))
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ)⟩
private def node_7 : Tree := .splitC (49 / 128 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitCValid box_7 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_5 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_5 : Tree := .splitD (23 / 64 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_1 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_1 : Tree := .splitC (73 / 192 : ℚ) node_2 node_5
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_5_accepts⟩

private def box_14 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (35 / 96 : ℚ), (47 / 128 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (361 / 1024 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (47 / 128 : ℚ), (283 / 768 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (283 / 768 : ℚ), (71 / 192 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_16 : Tree := .splitD (283 / 768 : ℚ) node_17 node_18
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (283 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_18_accepts⟩

private def box_20 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (47 / 128 : ℚ), (283 / 768 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (283 / 768 : ℚ), (71 / 192 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_19 : Tree := .splitD (283 / 768 : ℚ) node_20 node_21
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (283 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_21_accepts⟩

private def box_15 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_15 : Tree := .splitC (289 / 768 : ℚ) node_16 node_19
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_19_accepts⟩

private def box_13 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_13 : Tree := .splitD (47 / 128 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_23 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (35 / 96 : ℚ), (47 / 128 : ℚ)⟩
private def node_23 : Tree := .leaf (.strip (363 / 1024 : ℚ))
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (47 / 128 : ℚ), (283 / 768 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (283 / 768 : ℚ), (71 / 192 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_25 : Tree := .splitD (283 / 768 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitDValid box_25 (283 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_29 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (47 / 128 : ℚ), (283 / 768 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (283 / 768 : ℚ), (71 / 192 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_28 : Tree := .splitD (283 / 768 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (283 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_24 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_24 : Tree := .splitC (97 / 256 : ℚ) node_25 node_28
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_28_accepts⟩

private def box_22 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_22 : Tree := .splitD (47 / 128 : ℚ) node_23 node_24
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitDValid box_22 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_22], node_23_accepts, node_24_accepts⟩

private def box_12 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_12 : Tree := .splitC (145 / 384 : ℚ) node_13 node_22
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_22_accepts⟩

private def box_35 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_34 : Tree := .splitD (95 / 256 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_38 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_37 : Tree := .splitD (95 / 256 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_33 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_33 : Tree := .splitC (289 / 768 : ℚ) node_34 node_37
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitCValid box_33 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_33], node_34_accepts, node_37_accepts⟩

private def box_43 : Rectangle := ⟨(3 / 8 : ℚ), (577 / 1536 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(577 / 1536 : ℚ), (289 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_42 : Tree := .splitC (577 / 1536 : ℚ) node_43 node_44
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitCValid box_42 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_42], node_43_accepts, node_44_accepts⟩

private def box_46 : Rectangle := ⟨(3 / 8 : ℚ), (577 / 1536 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(577 / 1536 : ℚ), (289 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_45 : Tree := .splitC (577 / 1536 : ℚ) node_46 node_47
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitCValid box_45 (577 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_45], node_46_accepts, node_47_accepts⟩

private def box_41 : Rectangle := ⟨(3 / 8 : ℚ), (289 / 768 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_41 : Tree := .splitD (287 / 768 : ℚ) node_42 node_45
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitDValid box_41 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_41], node_42_accepts, node_45_accepts⟩

private def box_49 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(289 / 768 : ℚ), (145 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_48 : Tree := .splitD (287 / 768 : ℚ) node_49 node_50
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitDValid box_48 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_48], node_49_accepts, node_50_accepts⟩

private def box_40 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_40 : Tree := .splitC (289 / 768 : ℚ) node_41 node_48
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitCValid box_40 (289 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_40], node_41_accepts, node_48_accepts⟩

private def box_32 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_32 : Tree := .splitD (143 / 384 : ℚ) node_33 node_40
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitDValid box_32 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_32], node_33_accepts, node_40_accepts⟩

private def box_54 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_55 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_55 : Tree := .leaf .projection
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_53 : Tree := .splitD (95 / 256 : ℚ) node_54 node_55
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitDValid box_53 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_53], node_54_accepts, node_55_accepts⟩

private def box_57 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_56 : Tree := .splitD (95 / 256 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitDValid box_56 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_52 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_52 : Tree := .splitC (97 / 256 : ℚ) node_53 node_56
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitCValid box_52 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_52], node_53_accepts, node_56_accepts⟩

private def box_61 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_62 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_62 : Tree := .leaf .projection
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(145 / 384 : ℚ), (97 / 256 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_60 : Tree := .splitD (287 / 768 : ℚ) node_61 node_62
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitDValid box_60 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_60], node_61_accepts, node_62_accepts⟩

private def box_64 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_64 : Tree := .leaf .projection
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  norm_num [Tree.Accepts, node_64, box_64, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_65 : Tree := .leaf .projection
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(97 / 256 : ℚ), (73 / 192 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_63 : Tree := .splitD (287 / 768 : ℚ) node_64 node_65
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitDValid box_63 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_63], node_64_accepts, node_65_accepts⟩

private def box_59 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_59 : Tree := .splitC (97 / 256 : ℚ) node_60 node_63
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitCValid box_59 (97 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_59], node_60_accepts, node_63_accepts⟩

private def box_51 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_51 : Tree := .splitD (143 / 384 : ℚ) node_52 node_59
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitDValid box_51 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_51], node_52_accepts, node_59_accepts⟩

private def box_31 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_31 : Tree := .splitC (145 / 384 : ℚ) node_32 node_51
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_51_accepts⟩

private def box_11 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_11 : Tree := .splitD (71 / 192 : ℚ) node_12 node_31
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_31_accepts⟩

private def box_69 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (35 / 96 : ℚ), (47 / 128 : ℚ)⟩
private def node_69 : Tree := .leaf (.strip (365 / 1024 : ℚ))
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (47 / 128 : ℚ), (283 / 768 : ℚ)⟩
private def node_72 : Tree := .leaf .projection
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (283 / 768 : ℚ), (71 / 192 : ℚ)⟩
private def node_73 : Tree := .leaf .projection
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  norm_num [Tree.Accepts, node_73, box_73, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_71 : Tree := .splitD (283 / 768 : ℚ) node_72 node_73
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  change SplitDValid box_71 (283 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_71], node_72_accepts, node_73_accepts⟩

private def box_75 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (47 / 128 : ℚ), (283 / 768 : ℚ)⟩
private def node_75 : Tree := .leaf .projection
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (283 / 768 : ℚ), (71 / 192 : ℚ)⟩
private def node_76 : Tree := .leaf .projection
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_74 : Tree := .splitD (283 / 768 : ℚ) node_75 node_76
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitDValid box_74 (283 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_74], node_75_accepts, node_76_accepts⟩

private def box_70 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_70 : Tree := .splitC (293 / 768 : ℚ) node_71 node_74
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitCValid box_70 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_70], node_71_accepts, node_74_accepts⟩

private def box_68 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_68 : Tree := .splitD (47 / 128 : ℚ) node_69 node_70
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  change SplitDValid box_68 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_68], node_69_accepts, node_70_accepts⟩

private def box_79 : Rectangle := ⟨(49 / 128 : ℚ), (295 / 768 : ℚ), (35 / 96 : ℚ), (47 / 128 : ℚ)⟩
private def node_79 : Tree := .leaf .projection
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(295 / 768 : ℚ), (37 / 96 : ℚ), (35 / 96 : ℚ), (47 / 128 : ℚ)⟩
private def node_80 : Tree := .leaf .projection
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  norm_num [Tree.Accepts, node_80, box_80, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (35 / 96 : ℚ), (47 / 128 : ℚ)⟩
private def node_78 : Tree := .splitC (295 / 768 : ℚ) node_79 node_80
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  change SplitCValid box_78 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_78], node_79_accepts, node_80_accepts⟩

private def box_82 : Rectangle := ⟨(49 / 128 : ℚ), (295 / 768 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_82 : Tree := .leaf .projection
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(295 / 768 : ℚ), (37 / 96 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_83 : Tree := .leaf .projection
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_81 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ)⟩
private def node_81 : Tree := .splitC (295 / 768 : ℚ) node_82 node_83
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitCValid box_81 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_81], node_82_accepts, node_83_accepts⟩

private def box_77 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_77 : Tree := .splitD (47 / 128 : ℚ) node_78 node_81
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitDValid box_77 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_77], node_78_accepts, node_81_accepts⟩

private def box_67 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_67 : Tree := .splitC (49 / 128 : ℚ) node_68 node_77
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitCValid box_67 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_67], node_68_accepts, node_77_accepts⟩

private def box_88 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_88 : Tree := .leaf .projection
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  norm_num [Tree.Accepts, node_88, box_88, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_89 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_89 : Tree := .leaf .projection
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_87 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_87 : Tree := .splitD (95 / 256 : ℚ) node_88 node_89
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  change SplitDValid box_87 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_87], node_88_accepts, node_89_accepts⟩

private def box_91 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_91 : Tree := .leaf .projection
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  norm_num [Tree.Accepts, node_91, box_91, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_92 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_92 : Tree := .leaf .projection
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  norm_num [Tree.Accepts, node_92, box_92, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_90 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_90 : Tree := .splitD (95 / 256 : ℚ) node_91 node_92
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  change SplitDValid box_90 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_90], node_91_accepts, node_92_accepts⟩

private def box_86 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_86 : Tree := .splitC (293 / 768 : ℚ) node_87 node_90
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  change SplitCValid box_86 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_86], node_87_accepts, node_90_accepts⟩

private def box_95 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_95 : Tree := .leaf .projection
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  norm_num [Tree.Accepts, node_95, box_95, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_96 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_96 : Tree := .leaf .projection
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  norm_num [Tree.Accepts, node_96, box_96, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(73 / 192 : ℚ), (293 / 768 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_94 : Tree := .splitD (287 / 768 : ℚ) node_95 node_96
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  change SplitDValid box_94 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_94], node_95_accepts, node_96_accepts⟩

private def box_98 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_98 : Tree := .leaf .projection
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  norm_num [Tree.Accepts, node_98, box_98, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_99 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_99 : Tree := .leaf .projection
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  norm_num [Tree.Accepts, node_99, box_99, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_97 : Rectangle := ⟨(293 / 768 : ℚ), (49 / 128 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_97 : Tree := .splitD (287 / 768 : ℚ) node_98 node_99
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  change SplitDValid box_97 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_97], node_98_accepts, node_99_accepts⟩

private def box_93 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_93 : Tree := .splitC (293 / 768 : ℚ) node_94 node_97
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  change SplitCValid box_93 (293 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_93], node_94_accepts, node_97_accepts⟩

private def box_85 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_85 : Tree := .splitD (143 / 384 : ℚ) node_86 node_93
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  change SplitDValid box_85 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_85], node_86_accepts, node_93_accepts⟩

private def box_102 : Rectangle := ⟨(49 / 128 : ℚ), (295 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_102 : Tree := .leaf .projection
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  norm_num [Tree.Accepts, node_102, box_102, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_103 : Rectangle := ⟨(295 / 768 : ℚ), (37 / 96 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_103 : Tree := .leaf .projection
private theorem node_103_accepts : node_103.Accepts parameters box_103 := by
  norm_num [Tree.Accepts, node_103, box_103, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_101 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_101 : Tree := .splitC (295 / 768 : ℚ) node_102 node_103
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  change SplitCValid box_101 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_101], node_102_accepts, node_103_accepts⟩

private def box_106 : Rectangle := ⟨(49 / 128 : ℚ), (295 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_106 : Tree := .leaf .projection
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  norm_num [Tree.Accepts, node_106, box_106, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_107 : Rectangle := ⟨(49 / 128 : ℚ), (295 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_107 : Tree := .leaf .projection
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  norm_num [Tree.Accepts, node_107, box_107, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_105 : Rectangle := ⟨(49 / 128 : ℚ), (295 / 768 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_105 : Tree := .splitD (287 / 768 : ℚ) node_106 node_107
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  change SplitDValid box_105 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_105], node_106_accepts, node_107_accepts⟩

private def box_108 : Rectangle := ⟨(295 / 768 : ℚ), (37 / 96 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_108 : Tree := .leaf .projection
private theorem node_108_accepts : node_108.Accepts parameters box_108 := by
  norm_num [Tree.Accepts, node_108, box_108, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_104 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_104 : Tree := .splitC (295 / 768 : ℚ) node_105 node_108
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  change SplitCValid box_104 (295 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_104], node_105_accepts, node_108_accepts⟩

private def box_100 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_100 : Tree := .splitD (143 / 384 : ℚ) node_101 node_104
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  change SplitDValid box_100 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_100], node_101_accepts, node_104_accepts⟩

private def box_84 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_84 : Tree := .splitC (49 / 128 : ℚ) node_85 node_100
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  change SplitCValid box_84 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_84], node_85_accepts, node_100_accepts⟩

private def box_66 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_66 : Tree := .splitD (71 / 192 : ℚ) node_67 node_84
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitDValid box_66 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_66], node_67_accepts, node_84_accepts⟩

private def box_10 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_10 : Tree := .splitC (73 / 192 : ℚ) node_11 node_66
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitCValid box_10 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_10], node_11_accepts, node_66_accepts⟩

private def box_0 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_0 : Tree := .splitD (35 / 96 : ℚ) node_1 node_10
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_10_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C061
