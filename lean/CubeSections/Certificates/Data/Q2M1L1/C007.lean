import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L1.C007

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 1⟩

private def box_7 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (1 / 3 : ℚ), (11 / 32 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (139 / 512 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (11 / 32 : ℚ), (17 / 48 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (305 / 1024 : ℚ))
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_6 : Tree := .splitD (11 / 32 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_10 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (1 / 3 : ℚ), (11 / 32 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (17 / 64 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (11 / 32 : ℚ), (17 / 48 : ℚ)⟩
private def node_11 : Tree := .leaf (.strip (299 / 1024 : ℚ))
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_9 : Tree := .splitD (11 / 32 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitDValid box_9 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_5 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_5 : Tree := .splitC (41 / 96 : ℚ) node_6 node_9
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_9_accepts⟩

private def box_16 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (17 / 48 : ℚ), (23 / 64 : ℚ)⟩
private def node_16 : Tree := .leaf (.strip (77 / 256 : ℚ))
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ)⟩
private def node_17 : Tree := .leaf (.strip (317 / 1024 : ℚ))
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_15 : Tree := .splitD (23 / 64 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_18 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_18 : Tree := .leaf (.strip (159 / 512 : ℚ))
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_14 : Tree := .splitC (27 / 64 : ℚ) node_15 node_18
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitCValid box_14 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_14], node_15_accepts, node_18_accepts⟩

private def box_21 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_21 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_22 : Tree := .leaf (.strip (83 / 256 : ℚ))
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_20 : Tree := .splitD (71 / 192 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_24 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_24 : Tree := .leaf (.strip (323 / 1024 : ℚ))
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_25 : Tree := .leaf (.strip (165 / 512 : ℚ))
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_23 : Tree := .splitD (71 / 192 : ℚ) node_24 node_25
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitDValid box_23 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_23], node_24_accepts, node_25_accepts⟩

private def box_19 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_19 : Tree := .splitC (27 / 64 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitCValid box_19 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_13 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_13 : Tree := .splitD (35 / 96 : ℚ) node_14 node_19
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_19_accepts⟩

private def box_27 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_27 : Tree := .leaf (.strip (319 / 1024 : ℚ))
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(41 / 96 : ℚ), (83 / 192 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_30 : Tree := .leaf (.strip (5 / 16 : ℚ))
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(41 / 96 : ℚ), (83 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_31 : Tree := .leaf (.strip (327 / 1024 : ℚ))
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(41 / 96 : ℚ), (83 / 192 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_29 : Tree := .splitD (71 / 192 : ℚ) node_30 node_31
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitDValid box_29 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_29], node_30_accepts, node_31_accepts⟩

private def box_32 : Rectangle := ⟨(83 / 192 : ℚ), (7 / 16 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_32 : Tree := .leaf (.strip (327 / 1024 : ℚ))
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_28 : Tree := .splitC (83 / 192 : ℚ) node_29 node_32
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitCValid box_28 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_28], node_29_accepts, node_32_accepts⟩

private def box_26 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_26 : Tree := .splitD (35 / 96 : ℚ) node_27 node_28
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitDValid box_26 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_26], node_27_accepts, node_28_accepts⟩

private def box_12 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_12 : Tree := .splitC (41 / 96 : ℚ) node_13 node_26
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_26_accepts⟩

private def box_4 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_4 : Tree := .splitD (17 / 48 : ℚ) node_5 node_12
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_12_accepts⟩

private def box_35 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_35 : Tree := .leaf (.strip (147 / 512 : ℚ))
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_36 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_36 : Tree := .leaf (.strip (281 / 1024 : ℚ))
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_34 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_34 : Tree := .splitC (43 / 96 : ℚ) node_35 node_36
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitCValid box_34 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_34], node_35_accepts, node_36_accepts⟩

private def box_39 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_39 : Tree := .leaf (.strip (155 / 512 : ℚ))
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_40 : Tree := .leaf (.strip (163 / 512 : ℚ))
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  norm_num [Tree.Accepts, node_40, box_40, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_38 : Tree := .splitD (35 / 96 : ℚ) node_39 node_40
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  change SplitDValid box_38 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_38], node_39_accepts, node_40_accepts⟩

private def box_41 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_41 : Tree := .leaf (.strip (161 / 512 : ℚ))
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_37 : Tree := .splitC (43 / 96 : ℚ) node_38 node_41
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitCValid box_37 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_37], node_38_accepts, node_41_accepts⟩

private def box_33 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_33 : Tree := .splitD (17 / 48 : ℚ) node_34 node_37
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_37_accepts⟩

private def box_3 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_3 : Tree := .splitC (7 / 16 : ℚ) node_4 node_33
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_33_accepts⟩

private def box_49 : Rectangle := ⟨(5 / 12 : ℚ), (161 / 384 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_49 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(161 / 384 : ℚ), (27 / 64 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_50 : Tree := .leaf (.strip (167 / 512 : ℚ))
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_48 : Tree := .splitC (161 / 384 : ℚ) node_49 node_50
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitCValid box_48 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_48], node_49_accepts, node_50_accepts⟩

private def box_52 : Rectangle := ⟨(5 / 12 : ℚ), (161 / 384 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_52 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(161 / 384 : ℚ), (27 / 64 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_53 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_51 : Tree := .splitC (161 / 384 : ℚ) node_52 node_53
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitCValid box_51 (161 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_51], node_52_accepts, node_53_accepts⟩

private def box_47 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_47 : Tree := .splitD (73 / 192 : ℚ) node_48 node_51
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitDValid box_47 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_47], node_48_accepts, node_51_accepts⟩

private def box_55 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_55 : Tree := .leaf (.strip (21 / 64 : ℚ))
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_56 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_54 : Tree := .splitD (73 / 192 : ℚ) node_55 node_56
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitDValid box_54 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_54], node_55_accepts, node_56_accepts⟩

private def box_46 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_46 : Tree := .splitC (27 / 64 : ℚ) node_47 node_54
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitCValid box_46 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_46], node_47_accepts, node_54_accepts⟩

private def box_59 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_59 : Tree := .leaf (.strip (173 / 512 : ℚ))
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_60 : Tree := .leaf (.strip (349 / 1024 : ℚ))
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  norm_num [Tree.Accepts, node_60, box_60, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_58 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_58 : Tree := .splitD (25 / 64 : ℚ) node_59 node_60
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  change SplitDValid box_58 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_58], node_59_accepts, node_60_accepts⟩

private def box_62 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_62 : Tree := .leaf (.strip (43 / 128 : ℚ))
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_63 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_61 : Tree := .splitD (25 / 64 : ℚ) node_62 node_63
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitDValid box_61 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_61], node_62_accepts, node_63_accepts⟩

private def box_57 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_57 : Tree := .splitC (27 / 64 : ℚ) node_58 node_61
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitCValid box_57 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_57], node_58_accepts, node_61_accepts⟩

private def box_45 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_45 : Tree := .splitD (37 / 96 : ℚ) node_46 node_57
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitDValid box_45 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_45], node_46_accepts, node_57_accepts⟩

private def box_67 : Rectangle := ⟨(41 / 96 : ℚ), (83 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_67 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_68 : Rectangle := ⟨(41 / 96 : ℚ), (83 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_68 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(41 / 96 : ℚ), (83 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_66 : Tree := .splitD (73 / 192 : ℚ) node_67 node_68
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitDValid box_66 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_66], node_67_accepts, node_68_accepts⟩

private def box_69 : Rectangle := ⟨(83 / 192 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_69 : Tree := .leaf (.strip (169 / 512 : ℚ))
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_65 : Tree := .splitC (83 / 192 : ℚ) node_66 node_69
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitCValid box_65 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_65], node_66_accepts, node_69_accepts⟩

private def box_71 : Rectangle := ⟨(41 / 96 : ℚ), (83 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_71 : Tree := .leaf (.strip (349 / 1024 : ℚ))
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(83 / 192 : ℚ), (7 / 16 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_72 : Tree := .leaf (.strip (345 / 1024 : ℚ))
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_70 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_70 : Tree := .splitC (83 / 192 : ℚ) node_71 node_72
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitCValid box_70 (83 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_70], node_71_accepts, node_72_accepts⟩

private def box_64 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_64 : Tree := .splitD (37 / 96 : ℚ) node_65 node_70
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitDValid box_64 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_64], node_65_accepts, node_70_accepts⟩

private def box_44 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_44 : Tree := .splitC (41 / 96 : ℚ) node_45 node_64
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_64_accepts⟩

private def box_77 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_77 : Tree := .leaf (.strip (351 / 1024 : ℚ))
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  norm_num [Tree.Accepts, node_77, box_77, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_78 : Tree := .leaf (.strip (11 / 32 : ℚ))
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(5 / 12 : ℚ), (27 / 64 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_76 : Tree := .splitD (77 / 192 : ℚ) node_77 node_78
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  change SplitDValid box_76 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_76], node_77_accepts, node_78_accepts⟩

private def box_79 : Rectangle := ⟨(27 / 64 : ℚ), (41 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_79 : Tree := .leaf (.strip (89 / 256 : ℚ))
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_75 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_75 : Tree := .splitC (27 / 64 : ℚ) node_76 node_79
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  change SplitCValid box_75 (27 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_75], node_76_accepts, node_79_accepts⟩

private def box_80 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_80 : Tree := .leaf (.strip (91 / 256 : ℚ))
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  norm_num [Tree.Accepts, node_80, box_80, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_74 : Tree := .splitD (13 / 32 : ℚ) node_75 node_80
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitDValid box_74 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_74], node_75_accepts, node_80_accepts⟩

private def box_82 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_82 : Tree := .leaf (.strip (357 / 1024 : ℚ))
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_83 : Tree := .leaf (.strip (357 / 1024 : ℚ))
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_81 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_81 : Tree := .splitD (13 / 32 : ℚ) node_82 node_83
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitDValid box_81 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_81], node_82_accepts, node_83_accepts⟩

private def box_73 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_73 : Tree := .splitC (41 / 96 : ℚ) node_74 node_81
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitCValid box_73 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_73], node_74_accepts, node_81_accepts⟩

private def box_43 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_43 : Tree := .splitD (19 / 48 : ℚ) node_44 node_73
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_73_accepts⟩

private def box_87 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_87 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  norm_num [Tree.Accepts, node_87, box_87, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_88 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_88 : Tree := .leaf (.strip (345 / 1024 : ℚ))
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  norm_num [Tree.Accepts, node_88, box_88, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_86 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_86 : Tree := .splitD (37 / 96 : ℚ) node_87 node_88
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  change SplitDValid box_86 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_86], node_87_accepts, node_88_accepts⟩

private def box_90 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_90 : Tree := .leaf (.strip (325 / 1024 : ℚ))
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  norm_num [Tree.Accepts, node_90, box_90, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_91 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_91 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  norm_num [Tree.Accepts, node_91, box_91, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_89 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_89 : Tree := .splitD (37 / 96 : ℚ) node_90 node_91
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  change SplitDValid box_89 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_89], node_90_accepts, node_91_accepts⟩

private def box_85 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_85 : Tree := .splitC (43 / 96 : ℚ) node_86 node_89
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  change SplitCValid box_85 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_85], node_86_accepts, node_89_accepts⟩

private def box_94 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_94 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  norm_num [Tree.Accepts, node_94, box_94, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_95 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_95 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  norm_num [Tree.Accepts, node_95, box_95, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_93 : Rectangle := ⟨(7 / 16 : ℚ), (43 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_93 : Tree := .splitD (13 / 32 : ℚ) node_94 node_95
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  change SplitDValid box_93 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_93], node_94_accepts, node_95_accepts⟩

private def box_96 : Rectangle := ⟨(43 / 96 : ℚ), (11 / 24 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_96 : Tree := .leaf (.strip (175 / 512 : ℚ))
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  norm_num [Tree.Accepts, node_96, box_96, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_92 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_92 : Tree := .splitC (43 / 96 : ℚ) node_93 node_96
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  change SplitCValid box_92 (43 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_92], node_93_accepts, node_96_accepts⟩

private def box_84 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_84 : Tree := .splitD (19 / 48 : ℚ) node_85 node_92
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  change SplitDValid box_84 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_84], node_85_accepts, node_92_accepts⟩

private def box_42 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_42 : Tree := .splitC (7 / 16 : ℚ) node_43 node_84
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitCValid box_42 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_42], node_43_accepts, node_84_accepts⟩

private def box_2 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_2 : Tree := .splitD (3 / 8 : ℚ) node_3 node_42
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_42_accepts⟩

private def box_100 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_100 : Tree := .leaf (.strip (271 / 1024 : ℚ))
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  norm_num [Tree.Accepts, node_100, box_100, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_101 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_101 : Tree := .leaf (.strip (311 / 1024 : ℚ))
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  norm_num [Tree.Accepts, node_101, box_101, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_99 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_99 : Tree := .splitD (17 / 48 : ℚ) node_100 node_101
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  change SplitDValid box_99 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_99], node_100_accepts, node_101_accepts⟩

private def box_102 : Rectangle := ⟨(23 / 48 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_102 : Tree := .leaf (.strip (143 / 512 : ℚ))
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  norm_num [Tree.Accepts, node_102, box_102, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_98 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_98 : Tree := .splitC (23 / 48 : ℚ) node_99 node_102
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  change SplitCValid box_98 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_98], node_99_accepts, node_102_accepts⟩

private def box_105 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_105 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  norm_num [Tree.Accepts, node_105, box_105, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_106 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_106 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  norm_num [Tree.Accepts, node_106, box_106, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_104 : Rectangle := ⟨(11 / 24 : ℚ), (23 / 48 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_104 : Tree := .splitD (19 / 48 : ℚ) node_105 node_106
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  change SplitDValid box_104 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_104], node_105_accepts, node_106_accepts⟩

private def box_107 : Rectangle := ⟨(23 / 48 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_107 : Tree := .leaf (.strip (163 / 512 : ℚ))
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  norm_num [Tree.Accepts, node_107, box_107, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_103 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_103 : Tree := .splitC (23 / 48 : ℚ) node_104 node_107
private theorem node_103_accepts : node_103.Accepts parameters box_103 := by
  change SplitCValid box_103 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_103], node_104_accepts, node_107_accepts⟩

private def box_97 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_97 : Tree := .splitD (3 / 8 : ℚ) node_98 node_103
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  change SplitDValid box_97 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_97], node_98_accepts, node_103_accepts⟩

private def box_1 : Rectangle := ⟨(5 / 12 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_1 : Tree := .splitC (11 / 24 : ℚ) node_2 node_97
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_97_accepts⟩

private def box_113 : Rectangle := ⟨(5 / 12 : ℚ), (41 / 96 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_113 : Tree := .leaf (.strip (371 / 1024 : ℚ))
private theorem node_113_accepts : node_113.Accepts parameters box_113 := by
  norm_num [Tree.Accepts, node_113, box_113, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_114 : Rectangle := ⟨(41 / 96 : ℚ), (7 / 16 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_114 : Tree := .leaf (.strip (91 / 256 : ℚ))
private theorem node_114_accepts : node_114.Accepts parameters box_114 := by
  norm_num [Tree.Accepts, node_114, box_114, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_112 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_112 : Tree := .splitC (41 / 96 : ℚ) node_113 node_114
private theorem node_112_accepts : node_112.Accepts parameters box_112 := by
  change SplitCValid box_112 (41 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_112], node_113_accepts, node_114_accepts⟩

private def box_115 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_115 : Tree := .leaf (.strip (181 / 512 : ℚ))
private theorem node_115_accepts : node_115.Accepts parameters box_115 := by
  norm_num [Tree.Accepts, node_115, box_115, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_111 : Rectangle := ⟨(5 / 12 : ℚ), (7 / 16 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_111 : Tree := .splitD (7 / 16 : ℚ) node_112 node_115
private theorem node_111_accepts : node_111.Accepts parameters box_111 := by
  change SplitDValid box_111 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_111], node_112_accepts, node_115_accepts⟩

private def box_117 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (7 / 16 : ℚ)⟩
private def node_117 : Tree := .leaf (.strip (181 / 512 : ℚ))
private theorem node_117_accepts : node_117.Accepts parameters box_117 := by
  norm_num [Tree.Accepts, node_117, box_117, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_118 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (7 / 16 : ℚ), (11 / 24 : ℚ)⟩
private def node_118 : Tree := .leaf (.strip (43 / 128 : ℚ))
private theorem node_118_accepts : node_118.Accepts parameters box_118 := by
  norm_num [Tree.Accepts, node_118, box_118, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_116 : Rectangle := ⟨(7 / 16 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_116 : Tree := .splitD (7 / 16 : ℚ) node_117 node_118
private theorem node_116_accepts : node_116.Accepts parameters box_116 := by
  change SplitDValid box_116 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_116], node_117_accepts, node_118_accepts⟩

private def box_110 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_110 : Tree := .splitC (7 / 16 : ℚ) node_111 node_116
private theorem node_110_accepts : node_110.Accepts parameters box_110 := by
  change SplitCValid box_110 (7 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_110], node_111_accepts, node_116_accepts⟩

private def box_119 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_119 : Tree := .leaf (.strip (45 / 128 : ℚ))
private theorem node_119_accepts : node_119.Accepts parameters box_119 := by
  norm_num [Tree.Accepts, node_119, box_119, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_109 : Rectangle := ⟨(5 / 12 : ℚ), (11 / 24 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_109 : Tree := .splitD (11 / 24 : ℚ) node_110 node_119
private theorem node_109_accepts : node_109.Accepts parameters box_109 := by
  change SplitDValid box_109 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_109], node_110_accepts, node_119_accepts⟩

private def box_121 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_121 : Tree := .leaf (.strip (45 / 128 : ℚ))
private theorem node_121_accepts : node_121.Accepts parameters box_121 := by
  norm_num [Tree.Accepts, node_121, box_121, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_122 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_122 : Tree := .leaf (.strip (303 / 1024 : ℚ))
private theorem node_122_accepts : node_122.Accepts parameters box_122 := by
  norm_num [Tree.Accepts, node_122, box_122, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_120 : Rectangle := ⟨(11 / 24 : ℚ), (1 / 2 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_120 : Tree := .splitD (11 / 24 : ℚ) node_121 node_122
private theorem node_120_accepts : node_120.Accepts parameters box_120 := by
  change SplitDValid box_120 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_120], node_121_accepts, node_122_accepts⟩

private def box_108 : Rectangle := ⟨(5 / 12 : ℚ), (1 / 2 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_108 : Tree := .splitC (11 / 24 : ℚ) node_109 node_120
private theorem node_108_accepts : node_108.Accepts parameters box_108 := by
  change SplitCValid box_108 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_108], node_109_accepts, node_120_accepts⟩

private def box_0 : Rectangle := ⟨(5 / 12 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)⟩
private def node_0 : Tree := .splitD (5 / 12 : ℚ) node_1 node_108
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (5 / 12 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_108_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L1.C007
