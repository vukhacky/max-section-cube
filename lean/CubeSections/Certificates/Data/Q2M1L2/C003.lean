import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C003

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_1 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_1 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  norm_num [Tree.Accepts, node_1, box_1, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (21 / 64 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (169 / 512 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(11 / 32 : ℚ), (529 / 1536 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_9 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(529 / 1536 : ℚ), (265 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (171 / 512 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_8 : Tree := .splitC (529 / 1536 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitCValid box_8 (529 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_6 : Rectangle := ⟨(11 / 32 : ℚ), (265 / 768 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_6 : Tree := .splitD (287 / 768 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_12 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_12 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(265 / 768 : ℚ), (177 / 512 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (343 / 1024 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(177 / 512 : ℚ), (133 / 384 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_16 : Tree := .leaf (.strip (171 / 512 : ℚ))
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(177 / 512 : ℚ), (133 / 384 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(177 / 512 : ℚ), (133 / 384 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_15 : Tree := .splitD (575 / 1536 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_13 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_13 : Tree := .splitC (177 / 512 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitCValid box_13 (177 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_11 : Rectangle := ⟨(265 / 768 : ℚ), (133 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_11 : Tree := .splitD (287 / 768 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_5 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_5 : Tree := .splitC (265 / 768 : ℚ) node_6 node_11
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (265 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_11_accepts⟩

private def box_3 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_3 : Tree := .splitD (143 / 384 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_19 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_19 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_22 : Tree := .leaf (.strip (343 / 1024 : ℚ))
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_25 : Tree := .leaf (.strip (343 / 1024 : ℚ))
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(133 / 384 : ℚ), (355 / 1024 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(355 / 1024 : ℚ), (533 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_28 : Tree := .leaf .projection
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_26 : Tree := .splitC (355 / 1024 : ℚ) node_27 node_28
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitCValid box_26 (355 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_26], node_27_accepts, node_28_accepts⟩

private def box_24 : Rectangle := ⟨(133 / 384 : ℚ), (533 / 1536 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_24 : Tree := .splitD (575 / 1536 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_30 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_30 : Tree := .leaf (.strip (345 / 1024 : ℚ))
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(533 / 1536 : ℚ), (1067 / 3072 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(1067 / 3072 : ℚ), (89 / 256 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_33 : Tree := .leaf .projection
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_31 : Tree := .splitC (1067 / 3072 : ℚ) node_32 node_33
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitCValid box_31 (1067 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_31], node_32_accepts, node_33_accepts⟩

private def box_29 : Rectangle := ⟨(533 / 1536 : ℚ), (89 / 256 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_29 : Tree := .splitD (575 / 1536 : ℚ) node_30 node_31
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitDValid box_29 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_29], node_30_accepts, node_31_accepts⟩

private def box_23 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_23 : Tree := .splitC (533 / 1536 : ℚ) node_24 node_29
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitCValid box_23 (533 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_23], node_24_accepts, node_29_accepts⟩

private def box_21 : Rectangle := ⟨(133 / 384 : ℚ), (89 / 256 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_21 : Tree := .splitD (287 / 768 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_35 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_35 : Tree := .leaf (.strip (345 / 1024 : ℚ))
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_38 : Tree := .leaf (.strip (173 / 512 : ℚ))
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(89 / 256 : ℚ), (1069 / 3072 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_40 : Tree := .leaf .projection
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(1069 / 3072 : ℚ), (535 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_39 : Tree := .splitC (1069 / 3072 : ℚ) node_40 node_41
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitCValid box_39 (1069 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_39], node_40_accepts, node_41_accepts⟩

private def box_37 : Rectangle := ⟨(89 / 256 : ℚ), (535 / 1536 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_37 : Tree := .splitD (575 / 1536 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_44 : Rectangle := ⟨(535 / 1536 : ℚ), (357 / 1024 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_44 : Tree := .leaf (.strip (173 / 512 : ℚ))
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(357 / 1024 : ℚ), (67 / 192 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_45 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_43 : Tree := .splitC (357 / 1024 : ℚ) node_44 node_45
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitCValid box_43 (357 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_43], node_44_accepts, node_45_accepts⟩

private def box_47 : Rectangle := ⟨(535 / 1536 : ℚ), (357 / 1024 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(357 / 1024 : ℚ), (67 / 192 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_48 : Tree := .leaf .projection
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_46 : Tree := .splitC (357 / 1024 : ℚ) node_47 node_48
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (357 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_48_accepts⟩

private def box_42 : Rectangle := ⟨(535 / 1536 : ℚ), (67 / 192 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_42 : Tree := .splitD (575 / 1536 : ℚ) node_43 node_46
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitDValid box_42 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_42], node_43_accepts, node_46_accepts⟩

private def box_36 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_36 : Tree := .splitC (535 / 1536 : ℚ) node_37 node_42
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitCValid box_36 (535 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_36], node_37_accepts, node_42_accepts⟩

private def box_34 : Rectangle := ⟨(89 / 256 : ℚ), (67 / 192 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_34 : Tree := .splitD (287 / 768 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_20 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_20 : Tree := .splitC (89 / 256 : ℚ) node_21 node_34
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (89 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_34_accepts⟩

private def box_18 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_18 : Tree := .splitD (143 / 384 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_2 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_2 : Tree := .splitC (133 / 384 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (133 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_0 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_0 : Tree := .splitD (71 / 192 : ℚ) node_1 node_2
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_2_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C003
