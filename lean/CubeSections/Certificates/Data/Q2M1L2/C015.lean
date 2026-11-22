import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C015

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_2 : Rectangle := ⟨(23 / 64 : ℚ), (277 / 768 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_2 : Tree := .leaf (.strip (355 / 1024 : ℚ))
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  norm_num [Tree.Accepts, node_2, box_2, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(23 / 64 : ℚ), (553 / 1536 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (89 / 256 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(23 / 64 : ℚ), (553 / 1536 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (179 / 512 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(23 / 64 : ℚ), (553 / 1536 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_4 : Tree := .splitD (571 / 1536 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_8 : Rectangle := ⟨(553 / 1536 : ℚ), (277 / 768 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (357 / 1024 : ℚ))
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(553 / 1536 : ℚ), (369 / 1024 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(553 / 1536 : ℚ), (369 / 1024 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(553 / 1536 : ℚ), (369 / 1024 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_10 : Tree := .splitD (381 / 1024 : ℚ) node_11 node_12
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitDValid box_10 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_10], node_11_accepts, node_12_accepts⟩

private def box_13 : Rectangle := ⟨(369 / 1024 : ℚ), (277 / 768 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_13 : Tree := .leaf (.strip (359 / 1024 : ℚ))
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(553 / 1536 : ℚ), (277 / 768 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_9 : Tree := .splitC (369 / 1024 : ℚ) node_10 node_13
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (369 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_13_accepts⟩

private def box_7 : Rectangle := ⟨(553 / 1536 : ℚ), (277 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_7 : Tree := .splitD (571 / 1536 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitDValid box_7 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_3 : Rectangle := ⟨(23 / 64 : ℚ), (277 / 768 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_3 : Tree := .splitC (553 / 1536 : ℚ) node_4 node_7
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (553 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_7_accepts⟩

private def box_1 : Rectangle := ⟨(23 / 64 : ℚ), (277 / 768 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_1 : Tree := .splitD (95 / 256 : ℚ) node_2 node_3
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_3_accepts⟩

private def box_15 : Rectangle := ⟨(277 / 768 : ℚ), (139 / 384 : ℚ), (71 / 192 : ℚ), (95 / 256 : ℚ)⟩
private def node_15 : Tree := .leaf (.strip (357 / 1024 : ℚ))
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(277 / 768 : ℚ), (185 / 512 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_18 : Tree := .leaf (.strip (179 / 512 : ℚ))
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(277 / 768 : ℚ), (1109 / 3072 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_21 : Tree := .leaf .projection
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(277 / 768 : ℚ), (1109 / 3072 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(277 / 768 : ℚ), (1109 / 3072 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_20 : Tree := .splitD (381 / 1024 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_24 : Rectangle := ⟨(1109 / 3072 : ℚ), (185 / 512 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_24 : Tree := .leaf .projection
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(1109 / 3072 : ℚ), (185 / 512 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(1109 / 3072 : ℚ), (185 / 512 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_23 : Tree := .splitD (381 / 1024 : ℚ) node_24 node_25
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitDValid box_23 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_23], node_24_accepts, node_25_accepts⟩

private def box_19 : Rectangle := ⟨(277 / 768 : ℚ), (185 / 512 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_19 : Tree := .splitC (1109 / 3072 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitCValid box_19 (1109 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_17 : Rectangle := ⟨(277 / 768 : ℚ), (185 / 512 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_17 : Tree := .splitD (571 / 1536 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitDValid box_17 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_27 : Rectangle := ⟨(185 / 512 : ℚ), (139 / 384 : ℚ), (95 / 256 : ℚ), (571 / 1536 : ℚ)⟩
private def node_27 : Tree := .leaf (.strip (359 / 1024 : ℚ))
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(185 / 512 : ℚ), (1111 / 3072 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_29 : Tree := .leaf (.strip (45 / 128 : ℚ))
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(1111 / 3072 : ℚ), (139 / 384 : ℚ), (571 / 1536 : ℚ), (381 / 1024 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(1111 / 3072 : ℚ), (139 / 384 : ℚ), (381 / 1024 : ℚ), (143 / 384 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(1111 / 3072 : ℚ), (139 / 384 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_30 : Tree := .splitD (381 / 1024 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (381 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_28 : Rectangle := ⟨(185 / 512 : ℚ), (139 / 384 : ℚ), (571 / 1536 : ℚ), (143 / 384 : ℚ)⟩
private def node_28 : Tree := .splitC (1111 / 3072 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitCValid box_28 (1111 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_26 : Rectangle := ⟨(185 / 512 : ℚ), (139 / 384 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_26 : Tree := .splitD (571 / 1536 : ℚ) node_27 node_28
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitDValid box_26 (571 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_26], node_27_accepts, node_28_accepts⟩

private def box_16 : Rectangle := ⟨(277 / 768 : ℚ), (139 / 384 : ℚ), (95 / 256 : ℚ), (143 / 384 : ℚ)⟩
private def node_16 : Tree := .splitC (185 / 512 : ℚ) node_17 node_26
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitCValid box_16 (185 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_16], node_17_accepts, node_26_accepts⟩

private def box_14 : Rectangle := ⟨(277 / 768 : ℚ), (139 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_14 : Tree := .splitD (95 / 256 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitDValid box_14 (95 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_0 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_0 : Tree := .splitC (277 / 768 : ℚ) node_1 node_14
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (277 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_14_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C015
