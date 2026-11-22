import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L1.C005

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 1⟩

private def box_7 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (165 / 512 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_6 : Tree := .splitD (145 / 384 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_10 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (331 / 1024 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_11 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_9 : Tree := .splitD (145 / 384 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitDValid box_9 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_5 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_5 : Tree := .splitC (51 / 128 : ℚ) node_6 node_9
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_9_accepts⟩

private def box_14 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_15 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_13 : Tree := .splitD (49 / 128 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_17 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_17 : Tree := .leaf (.strip (21 / 64 : ℚ))
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_18 : Tree := .leaf (.strip (169 / 512 : ℚ))
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_16 : Tree := .splitD (49 / 128 : ℚ) node_17 node_18
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_18_accepts⟩

private def box_12 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_12 : Tree := .splitC (51 / 128 : ℚ) node_13 node_16
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_16_accepts⟩

private def box_4 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_4 : Tree := .splitD (73 / 192 : ℚ) node_5 node_12
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitDValid box_4 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_4], node_5_accepts, node_12_accepts⟩

private def box_22 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_22 : Tree := .leaf (.strip (331 / 1024 : ℚ))
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_23 : Tree := .leaf (.strip (167 / 512 : ℚ))
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_21 : Tree := .splitD (145 / 384 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_25 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_25 : Tree := .leaf (.strip (83 / 256 : ℚ))
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_26 : Tree := .leaf (.strip (167 / 512 : ℚ))
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_24 : Tree := .splitD (145 / 384 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_20 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_20 : Tree := .splitC (155 / 384 : ℚ) node_21 node_24
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_24_accepts⟩

private def box_29 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_29 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_30 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_28 : Tree := .splitD (49 / 128 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_32 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_32 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_33 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  norm_num [Tree.Accepts, node_33, box_33, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_31 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_31 : Tree := .splitD (49 / 128 : ℚ) node_32 node_33
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  change SplitDValid box_31 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_31], node_32_accepts, node_33_accepts⟩

private def box_27 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_27 : Tree := .splitC (155 / 384 : ℚ) node_28 node_31
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitCValid box_27 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_27], node_28_accepts, node_31_accepts⟩

private def box_19 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_19 : Tree := .splitD (73 / 192 : ℚ) node_20 node_27
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitDValid box_19 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_19], node_20_accepts, node_27_accepts⟩

private def box_3 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_3 : Tree := .splitC (77 / 192 : ℚ) node_4 node_19
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitCValid box_3 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_3], node_4_accepts, node_19_accepts⟩

private def box_38 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_38 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_39 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_37 : Tree := .splitD (149 / 384 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_41 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_41 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_42 : Tree := .leaf (.strip (171 / 512 : ℚ))
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_40 : Tree := .splitD (149 / 384 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_36 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_36 : Tree := .splitC (51 / 128 : ℚ) node_37 node_40
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitCValid box_36 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_36], node_37_accepts, node_40_accepts⟩

private def box_44 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_44 : Tree := .leaf (.strip (173 / 512 : ℚ))
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  norm_num [Tree.Accepts, node_44, box_44, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_45 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_43 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_43 : Tree := .splitC (51 / 128 : ℚ) node_44 node_45
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitCValid box_43 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_43], node_44_accepts, node_45_accepts⟩

private def box_35 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_35 : Tree := .splitD (25 / 64 : ℚ) node_36 node_43
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitDValid box_35 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_35], node_36_accepts, node_43_accepts⟩

private def box_49 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_49 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_50 : Tree := .leaf (.strip (171 / 512 : ℚ))
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_48 : Tree := .splitD (149 / 384 : ℚ) node_49 node_50
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitDValid box_48 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_48], node_49_accepts, node_50_accepts⟩

private def box_52 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_52 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  norm_num [Tree.Accepts, node_52, box_52, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_53 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_53 : Tree := .leaf (.strip (343 / 1024 : ℚ))
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_51 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_51 : Tree := .splitD (149 / 384 : ℚ) node_52 node_53
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitDValid box_51 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_51], node_52_accepts, node_53_accepts⟩

private def box_47 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_47 : Tree := .splitC (155 / 384 : ℚ) node_48 node_51
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitCValid box_47 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_47], node_48_accepts, node_51_accepts⟩

private def box_55 : Rectangle := ⟨(77 / 192 : ℚ), (155 / 384 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_55 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(155 / 384 : ℚ), (13 / 32 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_56 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_54 : Tree := .splitC (155 / 384 : ℚ) node_55 node_56
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitCValid box_54 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_54], node_55_accepts, node_56_accepts⟩

private def box_46 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_46 : Tree := .splitD (25 / 64 : ℚ) node_47 node_54
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  change SplitDValid box_46 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_46], node_47_accepts, node_54_accepts⟩

private def box_34 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_34 : Tree := .splitC (77 / 192 : ℚ) node_35 node_46
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitCValid box_34 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_34], node_35_accepts, node_46_accepts⟩

private def box_2 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_2 : Tree := .splitD (37 / 96 : ℚ) node_3 node_34
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitDValid box_2 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_2], node_3_accepts, node_34_accepts⟩

private def box_62 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_62 : Tree := .leaf (.strip (83 / 256 : ℚ))
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_63 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_61 : Tree := .splitD (145 / 384 : ℚ) node_62 node_63
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitDValid box_61 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_61], node_62_accepts, node_63_accepts⟩

private def box_65 : Rectangle := ⟨(157 / 384 : ℚ), (79 / 192 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_65 : Tree := .leaf (.strip (83 / 256 : ℚ))
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(157 / 384 : ℚ), (79 / 192 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_66 : Tree := .leaf (.strip (167 / 512 : ℚ))
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  norm_num [Tree.Accepts, node_66, box_66, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(157 / 384 : ℚ), (79 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_64 : Tree := .splitD (145 / 384 : ℚ) node_65 node_66
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  change SplitDValid box_64 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_64], node_65_accepts, node_66_accepts⟩

private def box_60 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_60 : Tree := .splitC (157 / 384 : ℚ) node_61 node_64
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitCValid box_60 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_60], node_61_accepts, node_64_accepts⟩

private def box_69 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_69 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_70 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_70 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  norm_num [Tree.Accepts, node_70, box_70, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_68 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_68 : Tree := .splitD (49 / 128 : ℚ) node_69 node_70
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  change SplitDValid box_68 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_68], node_69_accepts, node_70_accepts⟩

private def box_72 : Rectangle := ⟨(157 / 384 : ℚ), (79 / 192 : ℚ), (73 / 192 : ℚ), (49 / 128 : ℚ)⟩
private def node_72 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_73 : Rectangle := ⟨(157 / 384 : ℚ), (79 / 192 : ℚ), (49 / 128 : ℚ), (37 / 96 : ℚ)⟩
private def node_73 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  norm_num [Tree.Accepts, node_73, box_73, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(157 / 384 : ℚ), (79 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_71 : Tree := .splitD (49 / 128 : ℚ) node_72 node_73
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  change SplitDValid box_71 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_71], node_72_accepts, node_73_accepts⟩

private def box_67 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_67 : Tree := .splitC (157 / 384 : ℚ) node_68 node_71
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitCValid box_67 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_67], node_68_accepts, node_71_accepts⟩

private def box_59 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_59 : Tree := .splitD (73 / 192 : ℚ) node_60 node_67
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitDValid box_59 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_59], node_60_accepts, node_67_accepts⟩

private def box_76 : Rectangle := ⟨(79 / 192 : ℚ), (53 / 128 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_76 : Tree := .leaf (.strip (21 / 64 : ℚ))
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_77 : Rectangle := ⟨(53 / 128 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_77 : Tree := .leaf (.strip (21 / 64 : ℚ))
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  norm_num [Tree.Accepts, node_77, box_77, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_75 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_75 : Tree := .splitC (53 / 128 : ℚ) node_76 node_77
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  change SplitCValid box_75 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_75], node_76_accepts, node_77_accepts⟩

private def box_79 : Rectangle := ⟨(79 / 192 : ℚ), (53 / 128 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_79 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(53 / 128 : ℚ), (5 / 12 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_80 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  norm_num [Tree.Accepts, node_80, box_80, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_78 : Tree := .splitC (53 / 128 : ℚ) node_79 node_80
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  change SplitCValid box_78 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_78], node_79_accepts, node_80_accepts⟩

private def box_74 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_74 : Tree := .splitD (73 / 192 : ℚ) node_75 node_78
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitDValid box_74 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_74], node_75_accepts, node_78_accepts⟩

private def box_58 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_58 : Tree := .splitC (79 / 192 : ℚ) node_59 node_74
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  change SplitCValid box_58 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_58], node_59_accepts, node_74_accepts⟩

private def box_85 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (37 / 96 : ℚ), (149 / 384 : ℚ)⟩
private def node_85 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  norm_num [Tree.Accepts, node_85, box_85, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_86 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (149 / 384 : ℚ), (25 / 64 : ℚ)⟩
private def node_86 : Tree := .leaf (.strip (343 / 1024 : ℚ))
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  norm_num [Tree.Accepts, node_86, box_86, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_84 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_84 : Tree := .splitD (149 / 384 : ℚ) node_85 node_86
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  change SplitDValid box_84 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_84], node_85_accepts, node_86_accepts⟩

private def box_87 : Rectangle := ⟨(157 / 384 : ℚ), (79 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_87 : Tree := .leaf (.strip (345 / 1024 : ℚ))
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  norm_num [Tree.Accepts, node_87, box_87, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_83 : Tree := .splitC (157 / 384 : ℚ) node_84 node_87
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  change SplitCValid box_83 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_83], node_84_accepts, node_87_accepts⟩

private def box_89 : Rectangle := ⟨(13 / 32 : ℚ), (157 / 384 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_89 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  norm_num [Tree.Accepts, node_89, box_89, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_90 : Rectangle := ⟨(157 / 384 : ℚ), (79 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_90 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  norm_num [Tree.Accepts, node_90, box_90, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_88 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_88 : Tree := .splitC (157 / 384 : ℚ) node_89 node_90
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  change SplitCValid box_88 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_88], node_89_accepts, node_90_accepts⟩

private def box_82 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_82 : Tree := .splitD (25 / 64 : ℚ) node_83 node_88
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  change SplitDValid box_82 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_82], node_83_accepts, node_88_accepts⟩

private def box_93 : Rectangle := ⟨(79 / 192 : ℚ), (53 / 128 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_93 : Tree := .leaf (.strip (345 / 1024 : ℚ))
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  norm_num [Tree.Accepts, node_93, box_93, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(53 / 128 : ℚ), (5 / 12 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_94 : Tree := .leaf (.strip (43 / 128 : ℚ))
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  norm_num [Tree.Accepts, node_94, box_94, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_92 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_92 : Tree := .splitC (53 / 128 : ℚ) node_93 node_94
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  change SplitCValid box_92 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_92], node_93_accepts, node_94_accepts⟩

private def box_96 : Rectangle := ⟨(79 / 192 : ℚ), (53 / 128 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_96 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  norm_num [Tree.Accepts, node_96, box_96, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_97 : Rectangle := ⟨(53 / 128 : ℚ), (5 / 12 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_97 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  norm_num [Tree.Accepts, node_97, box_97, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_95 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_95 : Tree := .splitC (53 / 128 : ℚ) node_96 node_97
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  change SplitCValid box_95 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_95], node_96_accepts, node_97_accepts⟩

private def box_91 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_91 : Tree := .splitD (25 / 64 : ℚ) node_92 node_95
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  change SplitDValid box_91 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_91], node_92_accepts, node_95_accepts⟩

private def box_81 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_81 : Tree := .splitC (79 / 192 : ℚ) node_82 node_91
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitCValid box_81 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_81], node_82_accepts, node_91_accepts⟩

private def box_57 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_57 : Tree := .splitD (37 / 96 : ℚ) node_58 node_81
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitDValid box_57 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_57], node_58_accepts, node_81_accepts⟩

private def box_1 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_1 : Tree := .splitC (13 / 32 : ℚ) node_2 node_57
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitCValid box_1 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_1], node_2_accepts, node_57_accepts⟩

private def box_103 : Rectangle := ⟨(19 / 48 : ℚ), (51 / 128 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_103 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_103_accepts : node_103.Accepts parameters box_103 := by
  norm_num [Tree.Accepts, node_103, box_103, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_104 : Rectangle := ⟨(51 / 128 : ℚ), (77 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_104 : Tree := .leaf (.strip (349 / 1024 : ℚ))
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  norm_num [Tree.Accepts, node_104, box_104, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_102 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_102 : Tree := .splitC (51 / 128 : ℚ) node_103 node_104
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  change SplitCValid box_102 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_102], node_103_accepts, node_104_accepts⟩

private def box_105 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_105 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  norm_num [Tree.Accepts, node_105, box_105, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_101 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_101 : Tree := .splitD (77 / 192 : ℚ) node_102 node_105
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  change SplitDValid box_101 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_101], node_102_accepts, node_105_accepts⟩

private def box_107 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_107 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  norm_num [Tree.Accepts, node_107, box_107, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_108 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_108 : Tree := .leaf (.strip (177 / 512 : ℚ))
private theorem node_108_accepts : node_108.Accepts parameters box_108 := by
  norm_num [Tree.Accepts, node_108, box_108, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_106 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_106 : Tree := .splitD (77 / 192 : ℚ) node_107 node_108
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  change SplitDValid box_106 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_106], node_107_accepts, node_108_accepts⟩

private def box_100 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_100 : Tree := .splitC (77 / 192 : ℚ) node_101 node_106
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  change SplitCValid box_100 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_100], node_101_accepts, node_106_accepts⟩

private def box_111 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_111 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_111_accepts : node_111.Accepts parameters box_111 := by
  norm_num [Tree.Accepts, node_111, box_111, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_112 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_112 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_112_accepts : node_112.Accepts parameters box_112 := by
  norm_num [Tree.Accepts, node_112, box_112, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_110 : Rectangle := ⟨(19 / 48 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_110 : Tree := .splitD (79 / 192 : ℚ) node_111 node_112
private theorem node_110_accepts : node_110.Accepts parameters box_110 := by
  change SplitDValid box_110 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_110], node_111_accepts, node_112_accepts⟩

private def box_114 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_114 : Tree := .leaf (.strip (177 / 512 : ℚ))
private theorem node_114_accepts : node_114.Accepts parameters box_114 := by
  norm_num [Tree.Accepts, node_114, box_114, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_115 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_115 : Tree := .leaf (.strip (177 / 512 : ℚ))
private theorem node_115_accepts : node_115.Accepts parameters box_115 := by
  norm_num [Tree.Accepts, node_115, box_115, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_113 : Rectangle := ⟨(77 / 192 : ℚ), (13 / 32 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_113 : Tree := .splitD (79 / 192 : ℚ) node_114 node_115
private theorem node_113_accepts : node_113.Accepts parameters box_113 := by
  change SplitDValid box_113 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_113], node_114_accepts, node_115_accepts⟩

private def box_109 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_109 : Tree := .splitC (77 / 192 : ℚ) node_110 node_113
private theorem node_109_accepts : node_109.Accepts parameters box_109 := by
  change SplitCValid box_109 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_109], node_110_accepts, node_113_accepts⟩

private def box_99 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_99 : Tree := .splitD (13 / 32 : ℚ) node_100 node_109
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  change SplitDValid box_99 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_99], node_100_accepts, node_109_accepts⟩

private def box_119 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_119 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_119_accepts : node_119.Accepts parameters box_119 := by
  norm_num [Tree.Accepts, node_119, box_119, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_120 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_120 : Tree := .leaf (.strip (177 / 512 : ℚ))
private theorem node_120_accepts : node_120.Accepts parameters box_120 := by
  norm_num [Tree.Accepts, node_120, box_120, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_118 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_118 : Tree := .splitD (77 / 192 : ℚ) node_119 node_120
private theorem node_118_accepts : node_118.Accepts parameters box_118 := by
  change SplitDValid box_118 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_118], node_119_accepts, node_120_accepts⟩

private def box_122 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_122 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_122_accepts : node_122.Accepts parameters box_122 := by
  norm_num [Tree.Accepts, node_122, box_122, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_123 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_123 : Tree := .leaf (.strip (177 / 512 : ℚ))
private theorem node_123_accepts : node_123.Accepts parameters box_123 := by
  norm_num [Tree.Accepts, node_123, box_123, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_121 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_121 : Tree := .splitD (77 / 192 : ℚ) node_122 node_123
private theorem node_121_accepts : node_121.Accepts parameters box_121 := by
  change SplitDValid box_121 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_121], node_122_accepts, node_123_accepts⟩

private def box_117 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_117 : Tree := .splitC (79 / 192 : ℚ) node_118 node_121
private theorem node_117_accepts : node_117.Accepts parameters box_117 := by
  change SplitCValid box_117 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_117], node_118_accepts, node_121_accepts⟩

private def box_125 : Rectangle := ⟨(13 / 32 : ℚ), (79 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_125 : Tree := .leaf (.strip (361 / 1024 : ℚ))
private theorem node_125_accepts : node_125.Accepts parameters box_125 := by
  norm_num [Tree.Accepts, node_125, box_125, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_126 : Rectangle := ⟨(79 / 192 : ℚ), (5 / 12 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_126 : Tree := .leaf (.strip (45 / 128 : ℚ))
private theorem node_126_accepts : node_126.Accepts parameters box_126 := by
  norm_num [Tree.Accepts, node_126, box_126, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_124 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_124 : Tree := .splitC (79 / 192 : ℚ) node_125 node_126
private theorem node_124_accepts : node_124.Accepts parameters box_124 := by
  change SplitCValid box_124 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_124], node_125_accepts, node_126_accepts⟩

private def box_116 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_116 : Tree := .splitD (13 / 32 : ℚ) node_117 node_124
private theorem node_116_accepts : node_116.Accepts parameters box_116 := by
  change SplitDValid box_116 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_116], node_117_accepts, node_124_accepts⟩

private def box_98 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_98 : Tree := .splitC (13 / 32 : ℚ) node_99 node_116
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  change SplitCValid box_98 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_98], node_99_accepts, node_116_accepts⟩

private def box_0 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_0 : Tree := .splitD (19 / 48 : ℚ) node_1 node_98
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitDValid box_0 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_0], node_1_accepts, node_98_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L1.C005
