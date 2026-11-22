import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C017

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_2 : Rectangle := ⟨(139 / 384 : ℚ), (93 / 256 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_2 : Tree := .leaf (.strip (359 / 1024 : ℚ))
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  norm_num [Tree.Accepts, node_2, box_2, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(139 / 384 : ℚ), (557 / 1536 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (45 / 128 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(139 / 384 : ℚ), (371 / 1024 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(139 / 384 : ℚ), (371 / 1024 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(139 / 384 : ℚ), (371 / 1024 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_7 : Tree := .splitD (381 / 1024 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitDValid box_7 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_11 : Rectangle := ⟨(371 / 1024 : ℚ), (557 / 1536 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(371 / 1024 : ℚ), (557 / 1536 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(371 / 1024 : ℚ), (557 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_10 : Tree := .splitD (381 / 1024 : ℚ) node_11 node_12
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitDValid box_10 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_10], node_11_accepts, node_12_accepts⟩

private def box_6 : Rectangle := ⟨(139 / 384 : ℚ), (557 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_6 : Tree := .splitC (371 / 1024 : ℚ) node_7 node_10
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitCValid box_6 (371 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_6], node_7_accepts, node_10_accepts⟩

private def box_4 : Rectangle := ⟨(139 / 384 : ℚ), (557 / 1536 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_4 : Tree := .splitD (571 / 1536 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_14 : Rectangle := ⟨(557 / 1536 : ℚ), (93 / 256 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (45 / 128 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(557 / 1536 : ℚ), (1115 / 3072 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(557 / 1536 : ℚ), (1115 / 3072 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(557 / 1536 : ℚ), (1115 / 3072 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_16 : Tree := .splitD (381 / 1024 : ℚ) node_17 node_18
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_18_accepts⟩

private def box_20 : Rectangle := ⟨(1115 / 3072 : ℚ), (93 / 256 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(1115 / 3072 : ℚ), (93 / 256 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(1115 / 3072 : ℚ), (93 / 256 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_19 : Tree := .splitD (381 / 1024 : ℚ) node_20 node_21
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_21_accepts⟩

private def box_15 : Rectangle := ⟨(557 / 1536 : ℚ), (93 / 256 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_15 : Tree := .splitC (1115 / 3072 : ℚ) node_16 node_19
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (1115 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_19_accepts⟩

private def box_13 : Rectangle := ⟨(557 / 1536 : ℚ), (93 / 256 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_13 : Tree := .splitD (571 / 1536 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_3 : Rectangle := ⟨(139 / 384 : ℚ), (93 / 256 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_3 : Tree := .splitC (557 / 1536 : ℚ) node_4 node_13
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (557 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_13_accepts⟩

private def box_1 : Rectangle := ⟨(139 / 384 : ℚ), (93 / 256 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_1 : Tree := .splitD (95 / 256 : ℚ) node_2 node_3
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_3_accepts⟩

private def box_23 : Rectangle := ⟨(93 / 256 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_23 : Tree := .leaf (.strip (45 / 128 : ℚ))
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(93 / 256 : ℚ), (559 / 1536 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_26 : Tree := .leaf (.strip (361 / 1024 : ℚ))
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(93 / 256 : ℚ), (1117 / 3072 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(93 / 256 : ℚ), (1117 / 3072 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(93 / 256 : ℚ), (1117 / 3072 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_28 : Tree := .splitD (381 / 1024 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_32 : Rectangle := ⟨(1117 / 3072 : ℚ), (559 / 1536 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(1117 / 3072 : ℚ), (559 / 1536 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(1117 / 3072 : ℚ), (559 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_31 : Tree := .splitD (381 / 1024 : ℚ) node_32 node_33
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitDValid box_31 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_31], node_32_accepts, node_33_accepts⟩

private def box_27 : Rectangle := ⟨(93 / 256 : ℚ), (559 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_27 : Tree := .splitC (1117 / 3072 : ℚ) node_28 node_31
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitCValid box_27 (1117 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_27], node_28_accepts, node_31_accepts⟩

private def box_25 : Rectangle := ⟨(93 / 256 : ℚ), (559 / 1536 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_25 : Tree := .splitD (571 / 1536 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitDValid box_25 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_35 : Rectangle := ⟨(559 / 1536 : ℚ), (35 / 96 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_35 : Tree := .leaf (.strip (181 / 512 : ℚ))
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(559 / 1536 : ℚ), (373 / 1024 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(559 / 1536 : ℚ), (373 / 1024 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(559 / 1536 : ℚ), (373 / 1024 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_37 : Tree := .splitD (381 / 1024 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_41 : Rectangle := ⟨(373 / 1024 : ℚ), (35 / 96 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(373 / 1024 : ℚ), (35 / 96 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(373 / 1024 : ℚ), (35 / 96 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_40 : Tree := .splitD (381 / 1024 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_36 : Rectangle := ⟨(559 / 1536 : ℚ), (35 / 96 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_36 : Tree := .splitC (373 / 1024 : ℚ) node_37 node_40
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitCValid box_36 (373 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_36], node_37_accepts, node_40_accepts⟩

private def box_34 : Rectangle := ⟨(559 / 1536 : ℚ), (35 / 96 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_34 : Tree := .splitD (571 / 1536 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_24 : Rectangle := ⟨(93 / 256 : ℚ), (35 / 96 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_24 : Tree := .splitC (559 / 1536 : ℚ) node_25 node_34
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (559 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_34_accepts⟩

private def box_22 : Rectangle := ⟨(93 / 256 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_22 : Tree := .splitD (95 / 256 : ℚ) node_23 node_24
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitDValid box_22 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_22], node_23_accepts, node_24_accepts⟩

private def box_0 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_0 : Tree := .splitC (93 / 256 : ℚ) node_1 node_22
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (93 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_22_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C017
