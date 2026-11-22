import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q4M1L1

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨4, 1, 1⟩

private def box_5 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (149 / 1024 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (83 / 512 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_4 : Tree := .splitC (33 / 160 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_8 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (21 / 128 : ℚ))
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (17 / 80 : ℚ), (7 / 32 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (85 / 512 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (7 / 32 : ℚ), (9 / 40 : ℚ)⟩
private def node_11 : Tree := .leaf (.strip (173 / 1024 : ℚ))
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_9 : Tree := .splitD (7 / 32 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitDValid box_9 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_7 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_7 : Tree := .splitC (33 / 160 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitCValid box_7 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_3 : Tree := .splitD (17 / 80 : ℚ) node_4 node_7
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_7_accepts⟩

private def box_15 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_15 : Tree := .leaf (.strip (153 / 1024 : ℚ))
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_16 : Tree := .leaf (.strip (85 / 512 : ℚ))
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_14 : Tree := .splitD (33 / 160 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitDValid box_14 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_18 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_18 : Tree := .leaf (.strip (157 / 1024 : ℚ))
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_19 : Tree := .leaf (.strip (173 / 1024 : ℚ))
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_17 : Tree := .splitD (33 / 160 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitDValid box_17 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_13 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_13 : Tree := .splitC (7 / 32 : ℚ) node_14 node_17
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitCValid box_13 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_13], node_14_accepts, node_17_accepts⟩

private def box_22 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (17 / 80 : ℚ), (7 / 32 : ℚ)⟩
private def node_22 : Tree := .leaf (.strip (179 / 1024 : ℚ))
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (7 / 32 : ℚ), (9 / 40 : ℚ)⟩
private def node_23 : Tree := .leaf (.strip (91 / 512 : ℚ))
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_21 : Tree := .splitD (7 / 32 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_25 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (17 / 80 : ℚ), (7 / 32 : ℚ)⟩
private def node_25 : Tree := .leaf (.strip (91 / 512 : ℚ))
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (7 / 32 : ℚ), (9 / 40 : ℚ)⟩
private def node_26 : Tree := .leaf (.strip (93 / 512 : ℚ))
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_24 : Tree := .splitD (7 / 32 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_20 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_20 : Tree := .splitC (7 / 32 : ℚ) node_21 node_24
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_24_accepts⟩

private def box_12 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_12 : Tree := .splitD (17 / 80 : ℚ) node_13 node_20
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_20_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_2 : Tree := .splitC (17 / 80 : ℚ) node_3 node_12
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_12_accepts⟩

private def box_30 : Rectangle := ⟨(1 / 5 : ℚ), (33 / 160 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_30 : Tree := .leaf (.strip (41 / 256 : ℚ))
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(33 / 160 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_31 : Tree := .leaf (.strip (45 / 256 : ℚ))
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_29 : Tree := .splitC (33 / 160 : ℚ) node_30 node_31
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitCValid box_29 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_29], node_30_accepts, node_31_accepts⟩

private def box_32 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (19 / 80 : ℚ), (1 / 4 : ℚ)⟩
private def node_32 : Tree := .leaf (.strip (41 / 256 : ℚ))
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_28 : Tree := .splitD (19 / 80 : ℚ) node_29 node_32
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_32_accepts⟩

private def box_36 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (9 / 40 : ℚ), (37 / 160 : ℚ)⟩
private def node_36 : Tree := .leaf (.strip (181 / 1024 : ℚ))
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (37 / 160 : ℚ), (19 / 80 : ℚ)⟩
private def node_37 : Tree := .leaf (.strip (87 / 512 : ℚ))
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  norm_num [Tree.Accepts, node_37, box_37, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(17 / 80 : ℚ), (7 / 32 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_35 : Tree := .splitD (37 / 160 : ℚ) node_36 node_37
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitDValid box_35 (37 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_35], node_36_accepts, node_37_accepts⟩

private def box_38 : Rectangle := ⟨(7 / 32 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_38 : Tree := .leaf (.strip (3 / 16 : ℚ))
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_34 : Tree := .splitC (7 / 32 : ℚ) node_35 node_38
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitCValid box_34 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_34], node_35_accepts, node_38_accepts⟩

private def box_39 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ), (1 / 4 : ℚ)⟩
private def node_39 : Tree := .leaf (.strip (181 / 1024 : ℚ))
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_33 : Tree := .splitD (19 / 80 : ℚ) node_34 node_39
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_39_accepts⟩

private def box_27 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_27 : Tree := .splitC (17 / 80 : ℚ) node_28 node_33
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitCValid box_27 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_27], node_28_accepts, node_33_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_1 : Tree := .splitD (9 / 40 : ℚ) node_2 node_27
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_27_accepts⟩

private def box_45 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (1 / 5 : ℚ), (33 / 160 : ℚ)⟩
private def node_45 : Tree := .leaf (.strip (39 / 256 : ℚ))
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (33 / 160 : ℚ), (17 / 80 : ℚ)⟩
private def node_46 : Tree := .leaf (.strip (43 / 256 : ℚ))
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_44 : Tree := .splitD (33 / 160 : ℚ) node_45 node_46
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitDValid box_44 (33 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_44], node_45_accepts, node_46_accepts⟩

private def box_47 : Rectangle := ⟨(37 / 160 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_47 : Tree := .leaf (.strip (171 / 1024 : ℚ))
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_43 : Tree := .splitC (37 / 160 : ℚ) node_44 node_47
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitCValid box_43 (37 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_43], node_44_accepts, node_47_accepts⟩

private def box_50 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (17 / 80 : ℚ), (7 / 32 : ℚ)⟩
private def node_50 : Tree := .leaf (.strip (181 / 1024 : ℚ))
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (7 / 32 : ℚ), (9 / 40 : ℚ)⟩
private def node_51 : Tree := .leaf (.strip (23 / 128 : ℚ))
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(9 / 40 : ℚ), (37 / 160 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_49 : Tree := .splitD (7 / 32 : ℚ) node_50 node_51
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitDValid box_49 (7 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_49], node_50_accepts, node_51_accepts⟩

private def box_52 : Rectangle := ⟨(37 / 160 : ℚ), (19 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_52 : Tree := .leaf (.strip (47 / 256 : ℚ))
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_48 : Tree := .splitC (37 / 160 : ℚ) node_49 node_52
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitCValid box_48 (37 / 160 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_48], node_49_accepts, node_52_accepts⟩

private def box_42 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_42 : Tree := .splitD (17 / 80 : ℚ) node_43 node_48
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitDValid box_42 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_42], node_43_accepts, node_48_accepts⟩

private def box_54 : Rectangle := ⟨(19 / 80 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_54 : Tree := .leaf (.strip (41 / 256 : ℚ))
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_55 : Rectangle := ⟨(19 / 80 : ℚ), (1 / 4 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_55 : Tree := .leaf (.strip (181 / 1024 : ℚ))
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(19 / 80 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_53 : Tree := .splitD (17 / 80 : ℚ) node_54 node_55
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitDValid box_53 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_53], node_54_accepts, node_55_accepts⟩

private def box_41 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_41 : Tree := .splitC (19 / 80 : ℚ) node_42 node_53
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  change SplitCValid box_41 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_41], node_42_accepts, node_53_accepts⟩

private def box_58 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_58 : Tree := .leaf (.strip (99 / 512 : ℚ))
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (19 / 80 : ℚ), (1 / 4 : ℚ)⟩
private def node_59 : Tree := .leaf (.strip (177 / 1024 : ℚ))
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_57 : Tree := .splitD (19 / 80 : ℚ) node_58 node_59
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitDValid box_57 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_57], node_58_accepts, node_59_accepts⟩

private def box_60 : Rectangle := ⟨(19 / 80 : ℚ), (1 / 4 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_60 : Tree := .leaf (.strip (3 / 16 : ℚ))
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_56 : Tree := .splitC (19 / 80 : ℚ) node_57 node_60
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitCValid box_56 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_56], node_57_accepts, node_60_accepts⟩

private def box_40 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_40 : Tree := .splitD (9 / 40 : ℚ) node_41 node_56
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_56_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 5 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_0 : Tree := .splitC (9 / 40 : ℚ) node_1 node_40
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_40_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q4M1L1
