import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L1.C001

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 1⟩

private def box_4 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (267 / 1024 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (69 / 256 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_3 : Tree := .splitD (37 / 96 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_7 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (295 / 1024 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_9 : Tree := .leaf (.strip (9 / 32 : ℚ))
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (301 / 1024 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_8 : Tree := .splitC (67 / 192 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitCValid box_8 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_6 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_6 : Tree := .splitD (37 / 96 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_2 : Tree := .splitC (11 / 32 : ℚ) node_3 node_6
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_6_accepts⟩

private def box_13 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_13 : Tree := .leaf (.strip (35 / 128 : ℚ))
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (281 / 1024 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_12 : Tree := .splitD (13 / 32 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_17 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_17 : Tree := .leaf (.strip (293 / 1024 : ℚ))
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_18 : Tree := .leaf (.strip (305 / 1024 : ℚ))
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_16 : Tree := .splitC (67 / 192 : ℚ) node_17 node_18
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitCValid box_16 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_16], node_17_accepts, node_18_accepts⟩

private def box_20 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_20 : Tree := .leaf (.strip (293 / 1024 : ℚ))
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_21 : Tree := .leaf (.strip (305 / 1024 : ℚ))
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_19 : Tree := .splitC (67 / 192 : ℚ) node_20 node_21
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitCValid box_19 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_19], node_20_accepts, node_21_accepts⟩

private def box_15 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_15 : Tree := .splitD (13 / 32 : ℚ) node_16 node_19
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_19_accepts⟩

private def box_11 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_11 : Tree := .splitC (11 / 32 : ℚ) node_12 node_15
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitCValid box_11 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_11], node_12_accepts, node_15_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_1 : Tree := .splitD (19 / 48 : ℚ) node_2 node_11
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_11_accepts⟩

private def box_26 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_26 : Tree := .leaf (.strip (303 / 1024 : ℚ))
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_28 : Tree := .leaf (.strip (303 / 1024 : ℚ))
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_29 : Tree := .leaf (.strip (77 / 256 : ℚ))
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_27 : Tree := .splitD (73 / 192 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitDValid box_27 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_25 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_25 : Tree := .splitC (23 / 64 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitCValid box_25 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_32 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_32 : Tree := .leaf (.strip (303 / 1024 : ℚ))
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_33 : Tree := .leaf (.strip (153 / 512 : ℚ))
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_31 : Tree := .splitD (25 / 64 : ℚ) node_32 node_33
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitDValid box_31 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_31], node_32_accepts, node_33_accepts⟩

private def box_35 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_35 : Tree := .leaf (.strip (39 / 128 : ℚ))
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_36 : Tree := .leaf (.strip (315 / 1024 : ℚ))
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_34 : Tree := .splitD (25 / 64 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_30 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_30 : Tree := .splitC (23 / 64 : ℚ) node_31 node_34
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitCValid box_30 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_30], node_31_accepts, node_34_accepts⟩

private def box_24 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_24 : Tree := .splitD (37 / 96 : ℚ) node_25 node_30
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_30_accepts⟩

private def box_40 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_40 : Tree := .leaf (.strip (311 / 1024 : ℚ))
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_41 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_41 : Tree := .leaf (.strip (79 / 256 : ℚ))
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_39 : Tree := .splitD (73 / 192 : ℚ) node_40 node_41
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitDValid box_39 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_39], node_40_accepts, node_41_accepts⟩

private def box_43 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_43 : Tree := .leaf (.strip (319 / 1024 : ℚ))
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  norm_num [Tree.Accepts, node_43, box_43, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_45 : Tree := .leaf (.strip (159 / 512 : ℚ))
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_46 : Tree := .leaf (.strip (161 / 512 : ℚ))
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_44 : Tree := .splitC (143 / 384 : ℚ) node_45 node_46
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_46_accepts⟩

private def box_42 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_42 : Tree := .splitD (73 / 192 : ℚ) node_43 node_44
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitDValid box_42 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_42], node_43_accepts, node_44_accepts⟩

private def box_38 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_38 : Tree := .splitC (71 / 192 : ℚ) node_39 node_42
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitCValid box_38 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_38], node_39_accepts, node_42_accepts⟩

private def box_50 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_50 : Tree := .leaf (.strip (315 / 1024 : ℚ))
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_51 : Tree := .leaf (.strip (319 / 1024 : ℚ))
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  norm_num [Tree.Accepts, node_51, box_51, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_49 : Tree := .splitC (47 / 128 : ℚ) node_50 node_51
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  change SplitCValid box_49 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_49], node_50_accepts, node_51_accepts⟩

private def box_53 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_53 : Tree := .leaf (.strip (159 / 512 : ℚ))
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_54 : Tree := .leaf (.strip (161 / 512 : ℚ))
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_52 : Tree := .splitC (47 / 128 : ℚ) node_53 node_54
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitCValid box_52 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_52], node_53_accepts, node_54_accepts⟩

private def box_48 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_48 : Tree := .splitD (25 / 64 : ℚ) node_49 node_52
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitDValid box_48 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_48], node_49_accepts, node_52_accepts⟩

private def box_57 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_57 : Tree := .leaf (.strip (161 / 512 : ℚ))
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_58 : Tree := .leaf (.strip (163 / 512 : ℚ))
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_56 : Tree := .splitC (143 / 384 : ℚ) node_57 node_58
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  change SplitCValid box_56 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_56], node_57_accepts, node_58_accepts⟩

private def box_60 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_60 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_62 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (25 / 64 : ℚ), (151 / 384 : ℚ)⟩
private def node_62 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ)⟩
private def node_63 : Tree := .leaf (.strip (163 / 512 : ℚ))
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_61 : Tree := .splitD (151 / 384 : ℚ) node_62 node_63
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitDValid box_61 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_61], node_62_accepts, node_63_accepts⟩

private def box_59 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_59 : Tree := .splitC (143 / 384 : ℚ) node_60 node_61
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitCValid box_59 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_59], node_60_accepts, node_61_accepts⟩

private def box_55 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_55 : Tree := .splitD (25 / 64 : ℚ) node_56 node_59
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitDValid box_55 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_55], node_56_accepts, node_59_accepts⟩

private def box_47 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_47 : Tree := .splitC (71 / 192 : ℚ) node_48 node_55
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitCValid box_47 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_47], node_48_accepts, node_55_accepts⟩

private def box_37 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_37 : Tree := .splitD (37 / 96 : ℚ) node_38 node_47
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_47_accepts⟩

private def box_23 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_23 : Tree := .splitC (35 / 96 : ℚ) node_24 node_37
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitCValid box_23 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_23], node_24_accepts, node_37_accepts⟩

private def box_68 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_68 : Tree := .leaf (.strip (77 / 256 : ℚ))
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_69 : Tree := .leaf (.strip (309 / 1024 : ℚ))
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_67 : Tree := .splitD (77 / 192 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitDValid box_67 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_71 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_71 : Tree := .leaf (.strip (317 / 1024 : ℚ))
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_73 : Tree := .leaf (.strip (313 / 1024 : ℚ))
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  norm_num [Tree.Accepts, node_73, box_73, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_74 : Tree := .leaf (.strip (317 / 1024 : ℚ))
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  norm_num [Tree.Accepts, node_74, box_74, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_72 : Tree := .splitC (139 / 384 : ℚ) node_73 node_74
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitCValid box_72 (139 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_72], node_73_accepts, node_74_accepts⟩

private def box_70 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_70 : Tree := .splitD (77 / 192 : ℚ) node_71 node_72
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitDValid box_70 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_70], node_71_accepts, node_72_accepts⟩

private def box_66 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_66 : Tree := .splitC (23 / 64 : ℚ) node_67 node_70
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitCValid box_66 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_66], node_67_accepts, node_70_accepts⟩

private def box_77 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_77 : Tree := .leaf (.strip (155 / 512 : ℚ))
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  norm_num [Tree.Accepts, node_77, box_77, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_78 : Tree := .leaf (.strip (309 / 1024 : ℚ))
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_76 : Tree := .splitD (79 / 192 : ℚ) node_77 node_78
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  change SplitDValid box_76 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_76], node_77_accepts, node_78_accepts⟩

private def box_80 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_80 : Tree := .leaf (.strip (319 / 1024 : ℚ))
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  norm_num [Tree.Accepts, node_80, box_80, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_81 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_81 : Tree := .leaf (.strip (159 / 512 : ℚ))
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  norm_num [Tree.Accepts, node_81, box_81, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_79 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_79 : Tree := .splitD (79 / 192 : ℚ) node_80 node_81
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  change SplitDValid box_79 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_79], node_80_accepts, node_81_accepts⟩

private def box_75 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_75 : Tree := .splitC (23 / 64 : ℚ) node_76 node_79
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  change SplitCValid box_75 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_75], node_76_accepts, node_79_accepts⟩

private def box_65 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_65 : Tree := .splitD (13 / 32 : ℚ) node_66 node_75
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitDValid box_65 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_65], node_66_accepts, node_75_accepts⟩

private def box_86 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_86 : Tree := .leaf (.strip (5 / 16 : ℚ))
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  norm_num [Tree.Accepts, node_86, box_86, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_87 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_87 : Tree := .leaf (.strip (81 / 256 : ℚ))
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  norm_num [Tree.Accepts, node_87, box_87, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_85 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_85 : Tree := .splitC (47 / 128 : ℚ) node_86 node_87
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  change SplitCValid box_85 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_85], node_86_accepts, node_87_accepts⟩

private def box_89 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_89 : Tree := .leaf (.strip (321 / 1024 : ℚ))
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_90 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_90 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  norm_num [Tree.Accepts, node_90, box_90, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_88 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_88 : Tree := .splitC (47 / 128 : ℚ) node_89 node_90
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  change SplitCValid box_88 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_88], node_89_accepts, node_90_accepts⟩

private def box_84 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_84 : Tree := .splitD (77 / 192 : ℚ) node_85 node_88
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  change SplitDValid box_84 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_84], node_85_accepts, node_88_accepts⟩

private def box_93 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_93 : Tree := .leaf (.strip (327 / 1024 : ℚ))
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  norm_num [Tree.Accepts, node_93, box_93, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_95 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_95 : Tree := .leaf (.strip (327 / 1024 : ℚ))
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  norm_num [Tree.Accepts, node_95, box_95, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_96 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_96 : Tree := .leaf (.strip (41 / 128 : ℚ))
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  norm_num [Tree.Accepts, node_96, box_96, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_94 : Tree := .splitD (51 / 128 : ℚ) node_95 node_96
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  change SplitDValid box_94 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_94], node_95_accepts, node_96_accepts⟩

private def box_92 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_92 : Tree := .splitC (143 / 384 : ℚ) node_93 node_94
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  change SplitCValid box_92 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_92], node_93_accepts, node_94_accepts⟩

private def box_99 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_99 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  norm_num [Tree.Accepts, node_99, box_99, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_100 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_100 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  norm_num [Tree.Accepts, node_100, box_100, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_98 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_98 : Tree := .splitD (155 / 384 : ℚ) node_99 node_100
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  change SplitDValid box_98 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_98], node_99_accepts, node_100_accepts⟩

private def box_102 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_102 : Tree := .leaf (.strip (41 / 128 : ℚ))
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  norm_num [Tree.Accepts, node_102, box_102, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_103 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_103 : Tree := .leaf (.strip (329 / 1024 : ℚ))
private theorem node_103_accepts : node_103.Accepts parameters box_103 := by
  norm_num [Tree.Accepts, node_103, box_103, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_101 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_101 : Tree := .splitD (155 / 384 : ℚ) node_102 node_103
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  change SplitDValid box_101 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_101], node_102_accepts, node_103_accepts⟩

private def box_97 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_97 : Tree := .splitC (143 / 384 : ℚ) node_98 node_101
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  change SplitCValid box_97 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_97], node_98_accepts, node_101_accepts⟩

private def box_91 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_91 : Tree := .splitD (77 / 192 : ℚ) node_92 node_97
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  change SplitDValid box_91 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_91], node_92_accepts, node_97_accepts⟩

private def box_83 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_83 : Tree := .splitC (71 / 192 : ℚ) node_84 node_91
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  change SplitCValid box_83 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_83], node_84_accepts, node_91_accepts⟩

private def box_107 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_107 : Tree := .leaf (.strip (321 / 1024 : ℚ))
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  norm_num [Tree.Accepts, node_107, box_107, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_108 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_108 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_108_accepts : node_108.Accepts parameters box_108 := by
  norm_num [Tree.Accepts, node_108, box_108, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_106 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_106 : Tree := .splitC (47 / 128 : ℚ) node_107 node_108
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  change SplitCValid box_106 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_106], node_107_accepts, node_108_accepts⟩

private def box_109 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_109 : Tree := .leaf (.strip (163 / 512 : ℚ))
private theorem node_109_accepts : node_109.Accepts parameters box_109 := by
  norm_num [Tree.Accepts, node_109, box_109, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_105 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_105 : Tree := .splitD (79 / 192 : ℚ) node_106 node_109
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  change SplitDValid box_105 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_105], node_106_accepts, node_109_accepts⟩

private def box_112 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_112 : Tree := .leaf (.strip (329 / 1024 : ℚ))
private theorem node_112_accepts : node_112.Accepts parameters box_112 := by
  norm_num [Tree.Accepts, node_112, box_112, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_113 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_113 : Tree := .leaf (.strip (83 / 256 : ℚ))
private theorem node_113_accepts : node_113.Accepts parameters box_113 := by
  norm_num [Tree.Accepts, node_113, box_113, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_111 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_111 : Tree := .splitC (143 / 384 : ℚ) node_112 node_113
private theorem node_111_accepts : node_111.Accepts parameters box_111 := by
  change SplitCValid box_111 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_111], node_112_accepts, node_113_accepts⟩

private def box_115 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_115 : Tree := .leaf (.strip (41 / 128 : ℚ))
private theorem node_115_accepts : node_115.Accepts parameters box_115 := by
  norm_num [Tree.Accepts, node_115, box_115, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_116 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_116 : Tree := .leaf (.strip (331 / 1024 : ℚ))
private theorem node_116_accepts : node_116.Accepts parameters box_116 := by
  norm_num [Tree.Accepts, node_116, box_116, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_114 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_114 : Tree := .splitC (143 / 384 : ℚ) node_115 node_116
private theorem node_114_accepts : node_114.Accepts parameters box_114 := by
  change SplitCValid box_114 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_114], node_115_accepts, node_116_accepts⟩

private def box_110 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_110 : Tree := .splitD (79 / 192 : ℚ) node_111 node_114
private theorem node_110_accepts : node_110.Accepts parameters box_110 := by
  change SplitDValid box_110 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_110], node_111_accepts, node_114_accepts⟩

private def box_104 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_104 : Tree := .splitC (71 / 192 : ℚ) node_105 node_110
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  change SplitCValid box_104 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_104], node_105_accepts, node_110_accepts⟩

private def box_82 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_82 : Tree := .splitD (13 / 32 : ℚ) node_83 node_104
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  change SplitDValid box_82 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_82], node_83_accepts, node_104_accepts⟩

private def box_64 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_64 : Tree := .splitC (35 / 96 : ℚ) node_65 node_82
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitCValid box_64 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_64], node_65_accepts, node_82_accepts⟩

private def box_22 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_22 : Tree := .splitD (19 / 48 : ℚ) node_23 node_64
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitDValid box_22 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_22], node_23_accepts, node_64_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_0 : Tree := .splitC (17 / 48 : ℚ) node_1 node_22
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_22_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L1.C001
