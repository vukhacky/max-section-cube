import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C021

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_3 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_3 : Tree := .leaf (.strip (181 / 512 : ℚ))
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  norm_num [Tree.Accepts, node_3, box_3, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (363 / 1024 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_8 : Tree := .splitD (381 / 1024 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_11 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_7 : Tree := .splitC (1121 / 3072 : ℚ) node_8 node_11
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitCValid box_7 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_7], node_8_accepts, node_11_accepts⟩

private def box_5 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_5 : Tree := .splitD (571 / 1536 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_13 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_13 : Tree := .leaf (.strip (91 / 256 : ℚ))
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(187 / 512 : ℚ), (1123 / 3072 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_15 : Tree := .leaf .projection
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(1123 / 3072 : ℚ), (281 / 768 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_14 : Tree := .splitC (1123 / 3072 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitCValid box_14 (1123 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_12 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_12 : Tree := .splitD (571 / 1536 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_4 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_4 : Tree := .splitC (187 / 512 : ℚ) node_5 node_12
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (187 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_12_accepts⟩

private def box_2 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_2 : Tree := .splitD (95 / 256 : ℚ) node_3 node_4
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_4_accepts⟩

private def box_18 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_18 : Tree := .leaf (.strip (91 / 256 : ℚ))
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(281 / 768 : ℚ), (375 / 1024 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(375 / 1024 : ℚ), (563 / 1536 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_21 : Tree := .splitC (375 / 1024 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitCValid box_21 (375 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_25 : Rectangle := ⟨(281 / 768 : ℚ), (375 / 1024 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(375 / 1024 : ℚ), (563 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_24 : Tree := .splitC (375 / 1024 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (375 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_20 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_20 : Tree := .splitD (571 / 1536 : ℚ) node_21 node_24
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_24_accepts⟩

private def box_28 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_28 : Tree := .leaf (.strip (365 / 1024 : ℚ))
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(563 / 1536 : ℚ), (1127 / 3072 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(1127 / 3072 : ℚ), (47 / 128 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_29 : Tree := .splitC (1127 / 3072 : ℚ) node_30 node_31
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitCValid box_29 (1127 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_29], node_30_accepts, node_31_accepts⟩

private def box_27 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_27 : Tree := .splitD (571 / 1536 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitDValid box_27 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_19 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_19 : Tree := .splitC (563 / 1536 : ℚ) node_20 node_27
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitCValid box_19 (563 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_19], node_20_accepts, node_27_accepts⟩

private def box_17 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_17 : Tree := .splitD (95 / 256 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitDValid box_17 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_1 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_1 : Tree := .splitC (281 / 768 : ℚ) node_2 node_17
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (281 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_17_accepts⟩

private def box_38 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (143 / 384 : ℚ), (1145 / 3072 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (1145 / 3072 : ℚ), (191 / 512 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_37 : Tree := .splitD (1145 / 3072 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (1145 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_40 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_36 : Tree := .splitC (1121 / 3072 : ℚ) node_37 node_40
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitCValid box_36 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_36], node_37_accepts, node_40_accepts⟩

private def box_42 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_43 : Tree := .leaf .projection
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_41 : Tree := .splitC (1121 / 3072 : ℚ) node_42 node_43
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitCValid box_41 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_41], node_42_accepts, node_43_accepts⟩

private def box_35 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_35 : Tree := .splitD (191 / 512 : ℚ) node_36 node_41
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitDValid box_35 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_35], node_36_accepts, node_41_accepts⟩

private def box_46 : Rectangle := ⟨(187 / 512 : ℚ), (1123 / 3072 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(1123 / 3072 : ℚ), (281 / 768 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_45 : Tree := .splitC (1123 / 3072 : ℚ) node_46 node_47
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitCValid box_45 (1123 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_45], node_46_accepts, node_47_accepts⟩

private def box_49 : Rectangle := ⟨(187 / 512 : ℚ), (1123 / 3072 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(1123 / 3072 : ℚ), (281 / 768 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_48 : Tree := .splitC (1123 / 3072 : ℚ) node_49 node_50
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitCValid box_48 (1123 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_48], node_49_accepts, node_50_accepts⟩

private def box_44 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_44 : Tree := .splitD (191 / 512 : ℚ) node_45 node_48
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitDValid box_44 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_44], node_45_accepts, node_48_accepts⟩

private def box_34 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_34 : Tree := .splitC (187 / 512 : ℚ) node_35 node_44
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitCValid box_34 (187 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_34], node_35_accepts, node_44_accepts⟩

private def box_54 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_55 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_55 : Tree := .leaf .projection
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_53 : Tree := .splitC (1121 / 3072 : ℚ) node_54 node_55
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitCValid box_53 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_53], node_54_accepts, node_55_accepts⟩

private def box_57 : Rectangle := ⟨(35 / 96 : ℚ), (1121 / 3072 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(1121 / 3072 : ℚ), (187 / 512 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_58 : Tree := .leaf .projection
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_56 : Tree := .splitC (1121 / 3072 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitCValid box_56 (1121 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_52 : Rectangle := ⟨(35 / 96 : ℚ), (187 / 512 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_52 : Tree := .splitD (575 / 1536 : ℚ) node_53 node_56
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitDValid box_52 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_52], node_53_accepts, node_56_accepts⟩

private def box_61 : Rectangle := ⟨(187 / 512 : ℚ), (1123 / 3072 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_61 : Tree := .leaf .projection
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  norm_num [Tree.Accepts, node_61, box_61, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_62 : Rectangle := ⟨(1123 / 3072 : ℚ), (281 / 768 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_62 : Tree := .leaf .projection
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_60 : Tree := .splitC (1123 / 3072 : ℚ) node_61 node_62
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitCValid box_60 (1123 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_60], node_61_accepts, node_62_accepts⟩

private def box_64 : Rectangle := ⟨(187 / 512 : ℚ), (1123 / 3072 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_64 : Tree := .leaf .projection
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  norm_num [Tree.Accepts, node_64, box_64, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(1123 / 3072 : ℚ), (281 / 768 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_65 : Tree := .leaf .projection
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_63 : Tree := .splitC (1123 / 3072 : ℚ) node_64 node_65
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitCValid box_63 (1123 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_63], node_64_accepts, node_65_accepts⟩

private def box_59 : Rectangle := ⟨(187 / 512 : ℚ), (281 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_59 : Tree := .splitD (575 / 1536 : ℚ) node_60 node_63
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitDValid box_59 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_59], node_60_accepts, node_63_accepts⟩

private def box_51 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_51 : Tree := .splitC (187 / 512 : ℚ) node_52 node_59
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitCValid box_51 (187 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_51], node_52_accepts, node_59_accepts⟩

private def box_33 : Rectangle := ⟨(35 / 96 : ℚ), (281 / 768 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_33 : Tree := .splitD (287 / 768 : ℚ) node_34 node_51
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_51_accepts⟩

private def box_70 : Rectangle := ⟨(281 / 768 : ℚ), (375 / 1024 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_70 : Tree := .leaf .projection
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  norm_num [Tree.Accepts, node_70, box_70, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(375 / 1024 : ℚ), (563 / 1536 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_69 : Tree := .splitC (375 / 1024 : ℚ) node_70 node_71
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  change SplitCValid box_69 (375 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_69], node_70_accepts, node_71_accepts⟩

private def box_73 : Rectangle := ⟨(281 / 768 : ℚ), (375 / 1024 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_73 : Tree := .leaf .projection
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  norm_num [Tree.Accepts, node_73, box_73, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(375 / 1024 : ℚ), (563 / 1536 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_74 : Tree := .leaf .projection
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  norm_num [Tree.Accepts, node_74, box_74, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_72 : Tree := .splitC (375 / 1024 : ℚ) node_73 node_74
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitCValid box_72 (375 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_72], node_73_accepts, node_74_accepts⟩

private def box_68 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_68 : Tree := .splitD (191 / 512 : ℚ) node_69 node_72
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  change SplitDValid box_68 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_68], node_69_accepts, node_72_accepts⟩

private def box_77 : Rectangle := ⟨(563 / 1536 : ℚ), (1127 / 3072 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_77 : Tree := .leaf .projection
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  norm_num [Tree.Accepts, node_77, box_77, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(1127 / 3072 : ℚ), (47 / 128 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_78 : Tree := .leaf .projection
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_76 : Tree := .splitC (1127 / 3072 : ℚ) node_77 node_78
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  change SplitCValid box_76 (1127 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_76], node_77_accepts, node_78_accepts⟩

private def box_79 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_79 : Tree := .leaf .projection
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_75 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_75 : Tree := .splitD (191 / 512 : ℚ) node_76 node_79
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  change SplitDValid box_75 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_75], node_76_accepts, node_79_accepts⟩

private def box_67 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_67 : Tree := .splitC (563 / 1536 : ℚ) node_68 node_75
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitCValid box_67 (563 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_67], node_68_accepts, node_75_accepts⟩

private def box_83 : Rectangle := ⟨(281 / 768 : ℚ), (375 / 1024 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_83 : Tree := .leaf .projection
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_84 : Rectangle := ⟨(375 / 1024 : ℚ), (563 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_84 : Tree := .leaf .projection
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  norm_num [Tree.Accepts, node_84, box_84, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_82 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_82 : Tree := .splitC (375 / 1024 : ℚ) node_83 node_84
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  change SplitCValid box_82 (375 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_82], node_83_accepts, node_84_accepts⟩

private def box_86 : Rectangle := ⟨(281 / 768 : ℚ), (375 / 1024 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_86 : Tree := .leaf .projection
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  norm_num [Tree.Accepts, node_86, box_86, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_87 : Rectangle := ⟨(375 / 1024 : ℚ), (563 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_87 : Tree := .leaf .projection
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  norm_num [Tree.Accepts, node_87, box_87, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_85 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_85 : Tree := .splitC (375 / 1024 : ℚ) node_86 node_87
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  change SplitCValid box_85 (375 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_85], node_86_accepts, node_87_accepts⟩

private def box_81 : Rectangle := ⟨(281 / 768 : ℚ), (563 / 1536 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_81 : Tree := .splitD (575 / 1536 : ℚ) node_82 node_85
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitDValid box_81 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_81], node_82_accepts, node_85_accepts⟩

private def box_89 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_89 : Tree := .leaf .projection
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_90 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_90 : Tree := .leaf .projection
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  norm_num [Tree.Accepts, node_90, box_90, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_88 : Rectangle := ⟨(563 / 1536 : ℚ), (47 / 128 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_88 : Tree := .splitD (575 / 1536 : ℚ) node_89 node_90
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  change SplitDValid box_88 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_88], node_89_accepts, node_90_accepts⟩

private def box_80 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_80 : Tree := .splitC (563 / 1536 : ℚ) node_81 node_88
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitCValid box_80 (563 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_80], node_81_accepts, node_88_accepts⟩

private def box_66 : Rectangle := ⟨(281 / 768 : ℚ), (47 / 128 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_66 : Tree := .splitD (287 / 768 : ℚ) node_67 node_80
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitDValid box_66 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_66], node_67_accepts, node_80_accepts⟩

private def box_32 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_32 : Tree := .splitC (281 / 768 : ℚ) node_33 node_66
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  change SplitCValid box_32 (281 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_32], node_33_accepts, node_66_accepts⟩

private def box_0 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_0 : Tree := .splitD (143 / 384 : ℚ) node_1 node_32
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_32_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C021
