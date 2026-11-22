import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L1.C004

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 1⟩

private def box_6 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (165 / 512 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (331 / 1024 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_5 : Tree := .splitD (51 / 128 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_9 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_9 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (333 / 1024 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_8 : Tree := .splitD (51 / 128 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_4 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_4 : Tree := .splitC (145 / 384 : ℚ) node_5 node_8
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_8_accepts⟩

private def box_13 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_13 : Tree := .leaf (.strip (331 / 1024 : ℚ))
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (83 / 256 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_12 : Tree := .splitD (155 / 384 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_16 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_16 : Tree := .leaf (.strip (167 / 512 : ℚ))
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_17 : Tree := .leaf (.strip (167 / 512 : ℚ))
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_15 : Tree := .splitD (155 / 384 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitDValid box_15 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_11 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_11 : Tree := .splitC (145 / 384 : ℚ) node_12 node_15
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitCValid box_11 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_11], node_12_accepts, node_15_accepts⟩

private def box_3 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_3 : Tree := .splitD (77 / 192 : ℚ) node_4 node_11
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_11_accepts⟩

private def box_21 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_21 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_22 : Tree := .leaf (.strip (21 / 64 : ℚ))
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_20 : Tree := .splitD (51 / 128 : ℚ) node_21 node_22
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_22_accepts⟩

private def box_24 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_24 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_25 : Tree := .leaf (.strip (169 / 512 : ℚ))
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_23 : Tree := .splitD (51 / 128 : ℚ) node_24 node_25
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitDValid box_23 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_23], node_24_accepts, node_25_accepts⟩

private def box_19 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_19 : Tree := .splitC (49 / 128 : ℚ) node_20 node_23
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  change SplitCValid box_19 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_19], node_20_accepts, node_23_accepts⟩

private def box_28 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_28 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  norm_num [Tree.Accepts, node_28, box_28, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_29 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_29 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_27 : Tree := .splitD (155 / 384 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitDValid box_27 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_31 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_31 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_32 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_30 : Tree := .splitD (155 / 384 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_26 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_26 : Tree := .splitC (49 / 128 : ℚ) node_27 node_30
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitCValid box_26 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_26], node_27_accepts, node_30_accepts⟩

private def box_18 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_18 : Tree := .splitD (77 / 192 : ℚ) node_19 node_26
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_26_accepts⟩

private def box_2 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_2 : Tree := .splitC (73 / 192 : ℚ) node_3 node_18
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_18_accepts⟩

private def box_36 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_36 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  norm_num [Tree.Accepts, node_36, box_36, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_38 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (13 / 32 : ℚ), (157 / 384 : ℚ)⟩
private def node_38 : Tree := .leaf (.strip (335 / 1024 : ℚ))
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (157 / 384 : ℚ), (79 / 192 : ℚ)⟩
private def node_39 : Tree := .leaf (.strip (167 / 512 : ℚ))
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_37 : Tree := .splitD (157 / 384 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_35 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_35 : Tree := .splitC (145 / 384 : ℚ) node_36 node_37
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitCValid box_35 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_35], node_36_accepts, node_37_accepts⟩

private def box_41 : Rectangle := ⟨(3 / 8 : ℚ), (145 / 384 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_41 : Tree := .leaf (.strip (167 / 512 : ℚ))
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(145 / 384 : ℚ), (73 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_42 : Tree := .leaf (.strip (337 / 1024 : ℚ))
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_40 : Tree := .splitC (145 / 384 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitCValid box_40 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_34 : Rectangle := ⟨(3 / 8 : ℚ), (73 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_34 : Tree := .splitD (79 / 192 : ℚ) node_35 node_40
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  change SplitDValid box_34 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_34], node_35_accepts, node_40_accepts⟩

private def box_45 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_45 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  norm_num [Tree.Accepts, node_45, box_45, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_46 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_46 : Tree := .leaf (.strip (171 / 512 : ℚ))
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_44 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_44 : Tree := .splitC (49 / 128 : ℚ) node_45 node_46
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_46_accepts⟩

private def box_48 : Rectangle := ⟨(73 / 192 : ℚ), (49 / 128 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_48 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  norm_num [Tree.Accepts, node_48, box_48, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_49 : Rectangle := ⟨(49 / 128 : ℚ), (37 / 96 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_49 : Tree := .leaf (.strip (171 / 512 : ℚ))
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_47 : Tree := .splitC (49 / 128 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitCValid box_47 (49 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_43 : Rectangle := ⟨(73 / 192 : ℚ), (37 / 96 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_43 : Tree := .splitD (79 / 192 : ℚ) node_44 node_47
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_47_accepts⟩

private def box_33 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_33 : Tree := .splitC (73 / 192 : ℚ) node_34 node_43
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitCValid box_33 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_33], node_34_accepts, node_43_accepts⟩

private def box_1 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_1 : Tree := .splitD (13 / 32 : ℚ) node_2 node_33
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_33_accepts⟩

private def box_55 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_55 : Tree := .leaf (.strip (339 / 1024 : ℚ))
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  norm_num [Tree.Accepts, node_55, box_55, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_56 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_56 : Tree := .leaf (.strip (85 / 256 : ℚ))
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_54 : Tree := .splitD (51 / 128 : ℚ) node_55 node_56
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitDValid box_54 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_54], node_55_accepts, node_56_accepts⟩

private def box_58 : Rectangle := ⟨(149 / 384 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ), (51 / 128 : ℚ)⟩
private def node_58 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  norm_num [Tree.Accepts, node_58, box_58, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_59 : Rectangle := ⟨(149 / 384 : ℚ), (25 / 64 : ℚ), (51 / 128 : ℚ), (77 / 192 : ℚ)⟩
private def node_59 : Tree := .leaf (.strip (171 / 512 : ℚ))
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  norm_num [Tree.Accepts, node_59, box_59, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(149 / 384 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_57 : Tree := .splitD (51 / 128 : ℚ) node_58 node_59
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  change SplitDValid box_57 (51 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_57], node_58_accepts, node_59_accepts⟩

private def box_53 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_53 : Tree := .splitC (149 / 384 : ℚ) node_54 node_57
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitCValid box_53 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_53], node_54_accepts, node_57_accepts⟩

private def box_62 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (77 / 192 : ℚ), (155 / 384 : ℚ)⟩
private def node_62 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (155 / 384 : ℚ), (13 / 32 : ℚ)⟩
private def node_63 : Tree := .leaf (.strip (341 / 1024 : ℚ))
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  norm_num [Tree.Accepts, node_63, box_63, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_61 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_61 : Tree := .splitD (155 / 384 : ℚ) node_62 node_63
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitDValid box_61 (155 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_61], node_62_accepts, node_63_accepts⟩

private def box_64 : Rectangle := ⟨(149 / 384 : ℚ), (25 / 64 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_64 : Tree := .leaf (.strip (173 / 512 : ℚ))
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  norm_num [Tree.Accepts, node_64, box_64, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_60 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_60 : Tree := .splitC (149 / 384 : ℚ) node_61 node_64
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitCValid box_60 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_60], node_61_accepts, node_64_accepts⟩

private def box_52 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_52 : Tree := .splitD (77 / 192 : ℚ) node_53 node_60
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitDValid box_52 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_52], node_53_accepts, node_60_accepts⟩

private def box_67 : Rectangle := ⟨(25 / 64 : ℚ), (151 / 384 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_67 : Tree := .leaf (.strip (173 / 512 : ℚ))
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  norm_num [Tree.Accepts, node_67, box_67, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_68 : Rectangle := ⟨(151 / 384 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_68 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_66 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ)⟩
private def node_66 : Tree := .splitC (151 / 384 : ℚ) node_67 node_68
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitCValid box_66 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_66], node_67_accepts, node_68_accepts⟩

private def box_70 : Rectangle := ⟨(25 / 64 : ℚ), (151 / 384 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_70 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  norm_num [Tree.Accepts, node_70, box_70, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_71 : Rectangle := ⟨(151 / 384 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_71 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (77 / 192 : ℚ), (13 / 32 : ℚ)⟩
private def node_69 : Tree := .splitC (151 / 384 : ℚ) node_70 node_71
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  change SplitCValid box_69 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_69], node_70_accepts, node_71_accepts⟩

private def box_65 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_65 : Tree := .splitD (77 / 192 : ℚ) node_66 node_69
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  change SplitDValid box_65 (77 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_65], node_66_accepts, node_69_accepts⟩

private def box_51 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_51 : Tree := .splitC (25 / 64 : ℚ) node_52 node_65
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitCValid box_51 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_51], node_52_accepts, node_65_accepts⟩

private def box_75 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_75 : Tree := .leaf (.strip (43 / 128 : ℚ))
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  norm_num [Tree.Accepts, node_75, box_75, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_76 : Rectangle := ⟨(149 / 384 : ℚ), (25 / 64 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_76 : Tree := .leaf (.strip (173 / 512 : ℚ))
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_74 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_74 : Tree := .splitC (149 / 384 : ℚ) node_75 node_76
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitCValid box_74 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_74], node_75_accepts, node_76_accepts⟩

private def box_78 : Rectangle := ⟨(37 / 96 : ℚ), (149 / 384 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_78 : Tree := .leaf (.strip (43 / 128 : ℚ))
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  norm_num [Tree.Accepts, node_78, box_78, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_79 : Rectangle := ⟨(149 / 384 : ℚ), (25 / 64 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_79 : Tree := .leaf (.strip (345 / 1024 : ℚ))
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_77 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_77 : Tree := .splitC (149 / 384 : ℚ) node_78 node_79
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitCValid box_77 (149 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_77], node_78_accepts, node_79_accepts⟩

private def box_73 : Rectangle := ⟨(37 / 96 : ℚ), (25 / 64 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_73 : Tree := .splitD (79 / 192 : ℚ) node_74 node_77
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitDValid box_73 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_73], node_74_accepts, node_77_accepts⟩

private def box_82 : Rectangle := ⟨(25 / 64 : ℚ), (151 / 384 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_82 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  norm_num [Tree.Accepts, node_82, box_82, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_83 : Rectangle := ⟨(151 / 384 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_83 : Tree := .leaf (.strip (349 / 1024 : ℚ))
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_81 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_81 : Tree := .splitC (151 / 384 : ℚ) node_82 node_83
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitCValid box_81 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_81], node_82_accepts, node_83_accepts⟩

private def box_85 : Rectangle := ⟨(25 / 64 : ℚ), (151 / 384 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_85 : Tree := .leaf (.strip (347 / 1024 : ℚ))
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  norm_num [Tree.Accepts, node_85, box_85, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_86 : Rectangle := ⟨(151 / 384 : ℚ), (19 / 48 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_86 : Tree := .leaf (.strip (87 / 256 : ℚ))
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  norm_num [Tree.Accepts, node_86, box_86, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_84 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_84 : Tree := .splitC (151 / 384 : ℚ) node_85 node_86
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  change SplitCValid box_84 (151 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_84], node_85_accepts, node_86_accepts⟩

private def box_80 : Rectangle := ⟨(25 / 64 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_80 : Tree := .splitD (79 / 192 : ℚ) node_81 node_84
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitDValid box_80 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_80], node_81_accepts, node_84_accepts⟩

private def box_72 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_72 : Tree := .splitC (25 / 64 : ℚ) node_73 node_80
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  change SplitCValid box_72 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_72], node_73_accepts, node_80_accepts⟩

private def box_50 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_50 : Tree := .splitD (13 / 32 : ℚ) node_51 node_72
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  change SplitDValid box_50 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_50], node_51_accepts, node_72_accepts⟩

private def box_0 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_0 : Tree := .splitC (37 / 96 : ℚ) node_1 node_50
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_50_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L1.C004
