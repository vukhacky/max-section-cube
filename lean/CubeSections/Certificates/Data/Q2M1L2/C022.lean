import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C022

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_3 : Rectangle := ⟨(47 / 128 : ℚ), (283 / 768 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_3 : Tree := .leaf (.strip (365 / 1024 : ℚ))
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  norm_num [Tree.Accepts, node_3, box_3, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_6 : Tree := .leaf .projection
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_5 : Tree := .splitD (571 / 1536 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_9 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_8 : Tree := .splitD (571 / 1536 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_4 : Rectangle := ⟨(47 / 128 : ℚ), (283 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_4 : Tree := .splitC (565 / 1536 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (565 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_2 : Rectangle := ⟨(47 / 128 : ℚ), (283 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_2 : Tree := .splitD (95 / 256 : ℚ) node_3 node_4
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_4_accepts⟩

private def box_13 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_13 : Tree := .leaf (.strip (365 / 1024 : ℚ))
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (183 / 512 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(283 / 768 : ℚ), (71 / 192 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_12 : Tree := .splitC (189 / 512 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (189 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_17 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_16 : Tree := .splitD (571 / 1536 : ℚ) node_17 node_18
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_18_accepts⟩

private def box_20 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_19 : Tree := .splitD (571 / 1536 : ℚ) node_20 node_21
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_21_accepts⟩

private def box_15 : Rectangle := ⟨(283 / 768 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_15 : Tree := .splitC (189 / 512 : ℚ) node_16 node_19
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (189 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_19_accepts⟩

private def box_11 : Rectangle := ⟨(283 / 768 : ℚ), (71 / 192 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_11 : Tree := .splitD (95 / 256 : ℚ) node_12 node_15
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_15_accepts⟩

private def box_1 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_1 : Tree := .splitC (283 / 768 : ℚ) node_2 node_11
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (283 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_11_accepts⟩

private def box_26 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_25 : Tree := .splitD (191 / 512 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitDValid box_25 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_29 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_28 : Tree := .splitD (191 / 512 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_24 : Rectangle := ⟨(47 / 128 : ℚ), (283 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_24 : Tree := .splitC (565 / 1536 : ℚ) node_25 node_28
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (565 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_28_accepts⟩

private def box_33 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(47 / 128 : ℚ), (565 / 1536 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_32 : Tree := .splitD (575 / 1536 : ℚ) node_33 node_34
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitDValid box_32 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_32], node_33_accepts, node_34_accepts⟩

private def box_36 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_36 : Tree := .leaf .projection
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_37 : Tree := .leaf .projection
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  norm_num [Tree.Accepts, node_37, box_37, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(565 / 1536 : ℚ), (283 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_35 : Tree := .splitD (575 / 1536 : ℚ) node_36 node_37
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitDValid box_35 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_35], node_36_accepts, node_37_accepts⟩

private def box_31 : Rectangle := ⟨(47 / 128 : ℚ), (283 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_31 : Tree := .splitC (565 / 1536 : ℚ) node_32 node_35
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (565 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_35_accepts⟩

private def box_23 : Rectangle := ⟨(47 / 128 : ℚ), (283 / 768 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_23 : Tree := .splitD (287 / 768 : ℚ) node_24 node_31
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitDValid box_23 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_23], node_24_accepts, node_31_accepts⟩

private def box_41 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_40 : Tree := .splitD (191 / 512 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_44 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_44 : Tree := .leaf .projection
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_45 : Tree := .leaf .projection
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_43 : Tree := .splitD (191 / 512 : ℚ) node_44 node_45
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_45_accepts⟩

private def box_39 : Rectangle := ⟨(283 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_39 : Tree := .splitC (189 / 512 : ℚ) node_40 node_43
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitCValid box_39 (189 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_39], node_40_accepts, node_43_accepts⟩

private def box_48 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(283 / 768 : ℚ), (189 / 512 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_47 : Tree := .splitD (575 / 1536 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_51 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_51 : Tree := .leaf .projection
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_52 : Tree := .leaf .projection
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(189 / 512 : ℚ), (71 / 192 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_50 : Tree := .splitD (575 / 1536 : ℚ) node_51 node_52
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitDValid box_50 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_50], node_51_accepts, node_52_accepts⟩

private def box_46 : Rectangle := ⟨(283 / 768 : ℚ), (71 / 192 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_46 : Tree := .splitC (189 / 512 : ℚ) node_47 node_50
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (189 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_50_accepts⟩

private def box_38 : Rectangle := ⟨(283 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_38 : Tree := .splitD (287 / 768 : ℚ) node_39 node_46
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitDValid box_38 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_38], node_39_accepts, node_46_accepts⟩

private def box_22 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_22 : Tree := .splitC (283 / 768 : ℚ) node_23 node_38
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitCValid box_22 (283 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_22], node_23_accepts, node_38_accepts⟩

private def box_0 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_0 : Tree := .splitD (143 / 384 : ℚ) node_1 node_22
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_22_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C022
