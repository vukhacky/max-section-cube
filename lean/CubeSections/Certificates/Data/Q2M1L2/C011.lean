import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C011

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_5 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (11 / 32 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_4 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_4 : Tree := .splitC (363 / 1024 : ℚ) node_5 node_6
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (363 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_6_accepts⟩

private def box_9 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (191 / 512 : ℚ), (1147 / 3072 : ℚ)⟩
private def node_9 : Tree := .leaf .projection
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  norm_num [Tree.Accepts, node_9, box_9, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (1147 / 3072 : ℚ), (287 / 768 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_8 : Tree := .splitD (1147 / 3072 : ℚ) node_9 node_10
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (1147 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_10_accepts⟩

private def box_12 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (191 / 512 : ℚ), (1147 / 3072 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (1147 / 3072 : ℚ), (287 / 768 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_11 : Tree := .splitD (1147 / 3072 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitDValid box_11 (1147 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_7 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_7 : Tree := .splitC (363 / 1024 : ℚ) node_8 node_11
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitCValid box_7 (363 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_7], node_8_accepts, node_11_accepts⟩

private def box_3 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_3 : Tree := .splitD (191 / 512 : ℚ) node_4 node_7
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_7_accepts⟩

private def box_16 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_16 : Tree := .leaf (.strip (353 / 1024 : ℚ))
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (143 / 384 : ℚ), (1145 / 3072 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (1145 / 3072 : ℚ), (191 / 512 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_17 : Tree := .splitD (1145 / 3072 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitDValid box_17 (1145 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_15 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_15 : Tree := .splitC (1091 / 3072 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (1091 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_22 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (191 / 512 : ℚ), (1147 / 3072 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (1147 / 3072 : ℚ), (287 / 768 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_21 : Tree := .splitD (1147 / 3072 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (1147 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_25 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (191 / 512 : ℚ), (1147 / 3072 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_26 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (1147 / 3072 : ℚ), (287 / 768 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_24 : Tree := .splitD (1147 / 3072 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (1147 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_20 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_20 : Tree := .splitC (1091 / 3072 : ℚ) node_21 node_24
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (1091 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_24_accepts⟩

private def box_14 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_14 : Tree := .splitD (191 / 512 : ℚ) node_15 node_20
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitDValid box_14 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_14], node_15_accepts, node_20_accepts⟩

private def box_2 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_2 : Tree := .splitC (545 / 1536 : ℚ) node_3 node_14
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (545 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_14_accepts⟩

private def box_31 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (287 / 768 : ℚ), (383 / 1024 : ℚ)⟩
private def node_31 : Tree := .leaf .projection
private theorem node_31_accepts : node_31.Accepts parameters box_31 := by
  norm_num [Tree.Accepts, node_31, box_31, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_32 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (383 / 1024 : ℚ), (575 / 1536 : ℚ)⟩
private def node_32 : Tree := .leaf .projection
private theorem node_32_accepts : node_32.Accepts parameters box_32 := by
  norm_num [Tree.Accepts, node_32, box_32, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_30 : Tree := .splitD (383 / 1024 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (383 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_34 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (287 / 768 : ℚ), (383 / 1024 : ℚ)⟩
private def node_34 : Tree := .leaf .projection
private theorem node_34_accepts : node_34.Accepts parameters box_34 := by
  norm_num [Tree.Accepts, node_34, box_34, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_35 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (383 / 1024 : ℚ), (575 / 1536 : ℚ)⟩
private def node_35 : Tree := .leaf .projection
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  norm_num [Tree.Accepts, node_35, box_35, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_33 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_33 : Tree := .splitD (383 / 1024 : ℚ) node_34 node_35
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (383 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_35_accepts⟩

private def box_29 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_29 : Tree := .splitC (363 / 1024 : ℚ) node_30 node_33
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  change SplitCValid box_29 (363 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_29], node_30_accepts, node_33_accepts⟩

private def box_38 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (575 / 1536 : ℚ), (1151 / 3072 : ℚ)⟩
private def node_38 : Tree := .leaf .projection
private theorem node_38_accepts : node_38.Accepts parameters box_38 := by
  norm_num [Tree.Accepts, node_38, box_38, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_39 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (1151 / 3072 : ℚ), (3 / 8 : ℚ)⟩
private def node_39 : Tree := .leaf .projection
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  norm_num [Tree.Accepts, node_39, box_39, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_37 : Rectangle := ⟨(17 / 48 : ℚ), (363 / 1024 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_37 : Tree := .splitD (1151 / 3072 : ℚ) node_38 node_39
private theorem node_37_accepts : node_37.Accepts parameters box_37 := by
  change SplitDValid box_37 (1151 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_37], node_38_accepts, node_39_accepts⟩

private def box_41 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (575 / 1536 : ℚ), (1151 / 3072 : ℚ)⟩
private def node_41 : Tree := .leaf .projection
private theorem node_41_accepts : node_41.Accepts parameters box_41 := by
  norm_num [Tree.Accepts, node_41, box_41, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_42 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (1151 / 3072 : ℚ), (3 / 8 : ℚ)⟩
private def node_42 : Tree := .leaf .projection
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  norm_num [Tree.Accepts, node_42, box_42, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_40 : Rectangle := ⟨(363 / 1024 : ℚ), (545 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_40 : Tree := .splitD (1151 / 3072 : ℚ) node_41 node_42
private theorem node_40_accepts : node_40.Accepts parameters box_40 := by
  change SplitDValid box_40 (1151 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_40], node_41_accepts, node_42_accepts⟩

private def box_36 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_36 : Tree := .splitC (363 / 1024 : ℚ) node_37 node_40
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitCValid box_36 (363 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_36], node_37_accepts, node_40_accepts⟩

private def box_28 : Rectangle := ⟨(17 / 48 : ℚ), (545 / 1536 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_28 : Tree := .splitD (575 / 1536 : ℚ) node_29 node_36
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_36_accepts⟩

private def box_46 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (287 / 768 : ℚ), (383 / 1024 : ℚ)⟩
private def node_46 : Tree := .leaf .projection
private theorem node_46_accepts : node_46.Accepts parameters box_46 := by
  norm_num [Tree.Accepts, node_46, box_46, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_47 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (383 / 1024 : ℚ), (575 / 1536 : ℚ)⟩
private def node_47 : Tree := .leaf .projection
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  norm_num [Tree.Accepts, node_47, box_47, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_45 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_45 : Tree := .splitD (383 / 1024 : ℚ) node_46 node_47
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitDValid box_45 (383 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_45], node_46_accepts, node_47_accepts⟩

private def box_49 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (287 / 768 : ℚ), (383 / 1024 : ℚ)⟩
private def node_49 : Tree := .leaf .projection
private theorem node_49_accepts : node_49.Accepts parameters box_49 := by
  norm_num [Tree.Accepts, node_49, box_49, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_50 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (383 / 1024 : ℚ), (575 / 1536 : ℚ)⟩
private def node_50 : Tree := .leaf .projection
private theorem node_50_accepts : node_50.Accepts parameters box_50 := by
  norm_num [Tree.Accepts, node_50, box_50, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_48 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_48 : Tree := .splitD (383 / 1024 : ℚ) node_49 node_50
private theorem node_48_accepts : node_48.Accepts parameters box_48 := by
  change SplitDValid box_48 (383 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_48], node_49_accepts, node_50_accepts⟩

private def box_44 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_44 : Tree := .splitC (1091 / 3072 : ℚ) node_45 node_48
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (1091 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_48_accepts⟩

private def box_53 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (575 / 1536 : ℚ), (1151 / 3072 : ℚ)⟩
private def node_53 : Tree := .leaf .projection
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  norm_num [Tree.Accepts, node_53, box_53, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_54 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (1151 / 3072 : ℚ), (3 / 8 : ℚ)⟩
private def node_54 : Tree := .leaf .projection
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  norm_num [Tree.Accepts, node_54, box_54, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_52 : Rectangle := ⟨(545 / 1536 : ℚ), (1091 / 3072 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_52 : Tree := .splitD (1151 / 3072 : ℚ) node_53 node_54
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitDValid box_52 (1151 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_52], node_53_accepts, node_54_accepts⟩

private def box_56 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (575 / 1536 : ℚ), (1151 / 3072 : ℚ)⟩
private def node_56 : Tree := .leaf .projection
private theorem node_56_accepts : node_56.Accepts parameters box_56 := by
  norm_num [Tree.Accepts, node_56, box_56, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_57 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (1151 / 3072 : ℚ), (3 / 8 : ℚ)⟩
private def node_57 : Tree := .leaf .projection
private theorem node_57_accepts : node_57.Accepts parameters box_57 := by
  norm_num [Tree.Accepts, node_57, box_57, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_55 : Rectangle := ⟨(1091 / 3072 : ℚ), (91 / 256 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_55 : Tree := .splitD (1151 / 3072 : ℚ) node_56 node_57
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitDValid box_55 (1151 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_55], node_56_accepts, node_57_accepts⟩

private def box_51 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_51 : Tree := .splitC (1091 / 3072 : ℚ) node_52 node_55
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitCValid box_51 (1091 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_51], node_52_accepts, node_55_accepts⟩

private def box_43 : Rectangle := ⟨(545 / 1536 : ℚ), (91 / 256 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_43 : Tree := .splitD (575 / 1536 : ℚ) node_44 node_51
private theorem node_43_accepts : node_43.Accepts parameters box_43 := by
  change SplitDValid box_43 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_43], node_44_accepts, node_51_accepts⟩

private def box_27 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_27 : Tree := .splitC (545 / 1536 : ℚ) node_28 node_43
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitCValid box_27 (545 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_27], node_28_accepts, node_43_accepts⟩

private def box_1 : Rectangle := ⟨(17 / 48 : ℚ), (91 / 256 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_1 : Tree := .splitD (287 / 768 : ℚ) node_2 node_27
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_27_accepts⟩

private def box_62 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_62 : Tree := .leaf (.strip (177 / 512 : ℚ))
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  norm_num [Tree.Accepts, node_62, box_62, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_64 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (143 / 384 : ℚ), (1145 / 3072 : ℚ)⟩
private def node_64 : Tree := .leaf .projection
private theorem node_64_accepts : node_64.Accepts parameters box_64 := by
  norm_num [Tree.Accepts, node_64, box_64, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_65 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (1145 / 3072 : ℚ), (191 / 512 : ℚ)⟩
private def node_65 : Tree := .leaf .projection
private theorem node_65_accepts : node_65.Accepts parameters box_65 := by
  norm_num [Tree.Accepts, node_65, box_65, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_63 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_63 : Tree := .splitD (1145 / 3072 : ℚ) node_64 node_65
private theorem node_63_accepts : node_63.Accepts parameters box_63 := by
  change SplitDValid box_63 (1145 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_63], node_64_accepts, node_65_accepts⟩

private def box_61 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_61 : Tree := .splitC (1093 / 3072 : ℚ) node_62 node_63
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitCValid box_61 (1093 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_61], node_62_accepts, node_63_accepts⟩

private def box_68 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (191 / 512 : ℚ), (1147 / 3072 : ℚ)⟩
private def node_68 : Tree := .leaf .projection
private theorem node_68_accepts : node_68.Accepts parameters box_68 := by
  norm_num [Tree.Accepts, node_68, box_68, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_69 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (1147 / 3072 : ℚ), (287 / 768 : ℚ)⟩
private def node_69 : Tree := .leaf .projection
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  norm_num [Tree.Accepts, node_69, box_69, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_67 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_67 : Tree := .splitD (1147 / 3072 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitDValid box_67 (1147 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_71 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (191 / 512 : ℚ), (1147 / 3072 : ℚ)⟩
private def node_71 : Tree := .leaf .projection
private theorem node_71_accepts : node_71.Accepts parameters box_71 := by
  norm_num [Tree.Accepts, node_71, box_71, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_72 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (1147 / 3072 : ℚ), (287 / 768 : ℚ)⟩
private def node_72 : Tree := .leaf .projection
private theorem node_72_accepts : node_72.Accepts parameters box_72 := by
  norm_num [Tree.Accepts, node_72, box_72, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_70 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_70 : Tree := .splitD (1147 / 3072 : ℚ) node_71 node_72
private theorem node_70_accepts : node_70.Accepts parameters box_70 := by
  change SplitDValid box_70 (1147 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_70], node_71_accepts, node_72_accepts⟩

private def box_66 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_66 : Tree := .splitC (1093 / 3072 : ℚ) node_67 node_70
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitCValid box_66 (1093 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_66], node_67_accepts, node_70_accepts⟩

private def box_60 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_60 : Tree := .splitD (191 / 512 : ℚ) node_61 node_66
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitDValid box_60 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_60], node_61_accepts, node_66_accepts⟩

private def box_76 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (143 / 384 : ℚ), (1145 / 3072 : ℚ)⟩
private def node_76 : Tree := .leaf .projection
private theorem node_76_accepts : node_76.Accepts parameters box_76 := by
  norm_num [Tree.Accepts, node_76, box_76, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_77 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (1145 / 3072 : ℚ), (191 / 512 : ℚ)⟩
private def node_77 : Tree := .leaf .projection
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  norm_num [Tree.Accepts, node_77, box_77, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_75 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_75 : Tree := .splitD (1145 / 3072 : ℚ) node_76 node_77
private theorem node_75_accepts : node_75.Accepts parameters box_75 := by
  change SplitDValid box_75 (1145 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_75], node_76_accepts, node_77_accepts⟩

private def box_79 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (143 / 384 : ℚ), (1145 / 3072 : ℚ)⟩
private def node_79 : Tree := .leaf .projection
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  norm_num [Tree.Accepts, node_79, box_79, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_80 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (1145 / 3072 : ℚ), (191 / 512 : ℚ)⟩
private def node_80 : Tree := .leaf .projection
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  norm_num [Tree.Accepts, node_80, box_80, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_78 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_78 : Tree := .splitD (1145 / 3072 : ℚ) node_79 node_80
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  change SplitDValid box_78 (1145 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_78], node_79_accepts, node_80_accepts⟩

private def box_74 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (143 / 384 : ℚ), (191 / 512 : ℚ)⟩
private def node_74 : Tree := .splitC (365 / 1024 : ℚ) node_75 node_78
private theorem node_74_accepts : node_74.Accepts parameters box_74 := by
  change SplitCValid box_74 (365 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_74], node_75_accepts, node_78_accepts⟩

private def box_83 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (191 / 512 : ℚ), (1147 / 3072 : ℚ)⟩
private def node_83 : Tree := .leaf .projection
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  norm_num [Tree.Accepts, node_83, box_83, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_84 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (1147 / 3072 : ℚ), (287 / 768 : ℚ)⟩
private def node_84 : Tree := .leaf .projection
private theorem node_84_accepts : node_84.Accepts parameters box_84 := by
  norm_num [Tree.Accepts, node_84, box_84, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_82 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_82 : Tree := .splitD (1147 / 3072 : ℚ) node_83 node_84
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  change SplitDValid box_82 (1147 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_82], node_83_accepts, node_84_accepts⟩

private def box_86 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (191 / 512 : ℚ), (1147 / 3072 : ℚ)⟩
private def node_86 : Tree := .leaf .projection
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  norm_num [Tree.Accepts, node_86, box_86, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_87 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (1147 / 3072 : ℚ), (287 / 768 : ℚ)⟩
private def node_87 : Tree := .leaf .projection
private theorem node_87_accepts : node_87.Accepts parameters box_87 := by
  norm_num [Tree.Accepts, node_87, box_87, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_85 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_85 : Tree := .splitD (1147 / 3072 : ℚ) node_86 node_87
private theorem node_85_accepts : node_85.Accepts parameters box_85 := by
  change SplitDValid box_85 (1147 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_85], node_86_accepts, node_87_accepts⟩

private def box_81 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (191 / 512 : ℚ), (287 / 768 : ℚ)⟩
private def node_81 : Tree := .splitC (365 / 1024 : ℚ) node_82 node_85
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitCValid box_81 (365 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_81], node_82_accepts, node_85_accepts⟩

private def box_73 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_73 : Tree := .splitD (191 / 512 : ℚ) node_74 node_81
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitDValid box_73 (191 / 512 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_73], node_74_accepts, node_81_accepts⟩

private def box_59 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (143 / 384 : ℚ), (287 / 768 : ℚ)⟩
private def node_59 : Tree := .splitC (547 / 1536 : ℚ) node_60 node_73
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitCValid box_59 (547 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_59], node_60_accepts, node_73_accepts⟩

private def box_92 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (287 / 768 : ℚ), (383 / 1024 : ℚ)⟩
private def node_92 : Tree := .leaf .projection
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  norm_num [Tree.Accepts, node_92, box_92, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_93 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (383 / 1024 : ℚ), (575 / 1536 : ℚ)⟩
private def node_93 : Tree := .leaf .projection
private theorem node_93_accepts : node_93.Accepts parameters box_93 := by
  norm_num [Tree.Accepts, node_93, box_93, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_91 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_91 : Tree := .splitD (383 / 1024 : ℚ) node_92 node_93
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  change SplitDValid box_91 (383 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_91], node_92_accepts, node_93_accepts⟩

private def box_95 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (287 / 768 : ℚ), (383 / 1024 : ℚ)⟩
private def node_95 : Tree := .leaf .projection
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  norm_num [Tree.Accepts, node_95, box_95, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_96 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (383 / 1024 : ℚ), (575 / 1536 : ℚ)⟩
private def node_96 : Tree := .leaf .projection
private theorem node_96_accepts : node_96.Accepts parameters box_96 := by
  norm_num [Tree.Accepts, node_96, box_96, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_94 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_94 : Tree := .splitD (383 / 1024 : ℚ) node_95 node_96
private theorem node_94_accepts : node_94.Accepts parameters box_94 := by
  change SplitDValid box_94 (383 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_94], node_95_accepts, node_96_accepts⟩

private def box_90 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_90 : Tree := .splitC (1093 / 3072 : ℚ) node_91 node_94
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  change SplitCValid box_90 (1093 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_90], node_91_accepts, node_94_accepts⟩

private def box_99 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (575 / 1536 : ℚ), (1151 / 3072 : ℚ)⟩
private def node_99 : Tree := .leaf .projection
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  norm_num [Tree.Accepts, node_99, box_99, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_100 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (1151 / 3072 : ℚ), (3 / 8 : ℚ)⟩
private def node_100 : Tree := .leaf .projection
private theorem node_100_accepts : node_100.Accepts parameters box_100 := by
  norm_num [Tree.Accepts, node_100, box_100, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_98 : Rectangle := ⟨(91 / 256 : ℚ), (1093 / 3072 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_98 : Tree := .splitD (1151 / 3072 : ℚ) node_99 node_100
private theorem node_98_accepts : node_98.Accepts parameters box_98 := by
  change SplitDValid box_98 (1151 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_98], node_99_accepts, node_100_accepts⟩

private def box_102 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (575 / 1536 : ℚ), (1151 / 3072 : ℚ)⟩
private def node_102 : Tree := .leaf .projection
private theorem node_102_accepts : node_102.Accepts parameters box_102 := by
  norm_num [Tree.Accepts, node_102, box_102, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_103 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (1151 / 3072 : ℚ), (3 / 8 : ℚ)⟩
private def node_103 : Tree := .leaf .projection
private theorem node_103_accepts : node_103.Accepts parameters box_103 := by
  norm_num [Tree.Accepts, node_103, box_103, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_101 : Rectangle := ⟨(1093 / 3072 : ℚ), (547 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_101 : Tree := .splitD (1151 / 3072 : ℚ) node_102 node_103
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  change SplitDValid box_101 (1151 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_101], node_102_accepts, node_103_accepts⟩

private def box_97 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_97 : Tree := .splitC (1093 / 3072 : ℚ) node_98 node_101
private theorem node_97_accepts : node_97.Accepts parameters box_97 := by
  change SplitCValid box_97 (1093 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_97], node_98_accepts, node_101_accepts⟩

private def box_89 : Rectangle := ⟨(91 / 256 : ℚ), (547 / 1536 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_89 : Tree := .splitD (575 / 1536 : ℚ) node_90 node_97
private theorem node_89_accepts : node_89.Accepts parameters box_89 := by
  change SplitDValid box_89 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_89], node_90_accepts, node_97_accepts⟩

private def box_107 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (287 / 768 : ℚ), (383 / 1024 : ℚ)⟩
private def node_107 : Tree := .leaf .projection
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  norm_num [Tree.Accepts, node_107, box_107, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_108 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (383 / 1024 : ℚ), (575 / 1536 : ℚ)⟩
private def node_108 : Tree := .leaf .projection
private theorem node_108_accepts : node_108.Accepts parameters box_108 := by
  norm_num [Tree.Accepts, node_108, box_108, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_106 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_106 : Tree := .splitD (383 / 1024 : ℚ) node_107 node_108
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  change SplitDValid box_106 (383 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_106], node_107_accepts, node_108_accepts⟩

private def box_110 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (287 / 768 : ℚ), (383 / 1024 : ℚ)⟩
private def node_110 : Tree := .leaf .projection
private theorem node_110_accepts : node_110.Accepts parameters box_110 := by
  norm_num [Tree.Accepts, node_110, box_110, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_111 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (383 / 1024 : ℚ), (575 / 1536 : ℚ)⟩
private def node_111 : Tree := .leaf .projection
private theorem node_111_accepts : node_111.Accepts parameters box_111 := by
  norm_num [Tree.Accepts, node_111, box_111, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_109 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_109 : Tree := .splitD (383 / 1024 : ℚ) node_110 node_111
private theorem node_109_accepts : node_109.Accepts parameters box_109 := by
  change SplitDValid box_109 (383 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_109], node_110_accepts, node_111_accepts⟩

private def box_105 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (287 / 768 : ℚ), (575 / 1536 : ℚ)⟩
private def node_105 : Tree := .splitC (365 / 1024 : ℚ) node_106 node_109
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  change SplitCValid box_105 (365 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_105], node_106_accepts, node_109_accepts⟩

private def box_114 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (575 / 1536 : ℚ), (1151 / 3072 : ℚ)⟩
private def node_114 : Tree := .leaf .projection
private theorem node_114_accepts : node_114.Accepts parameters box_114 := by
  norm_num [Tree.Accepts, node_114, box_114, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_115 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (1151 / 3072 : ℚ), (3 / 8 : ℚ)⟩
private def node_115 : Tree := .leaf .projection
private theorem node_115_accepts : node_115.Accepts parameters box_115 := by
  norm_num [Tree.Accepts, node_115, box_115, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_113 : Rectangle := ⟨(547 / 1536 : ℚ), (365 / 1024 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_113 : Tree := .splitD (1151 / 3072 : ℚ) node_114 node_115
private theorem node_113_accepts : node_113.Accepts parameters box_113 := by
  change SplitDValid box_113 (1151 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_113], node_114_accepts, node_115_accepts⟩

private def box_117 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (575 / 1536 : ℚ), (1151 / 3072 : ℚ)⟩
private def node_117 : Tree := .leaf .projection
private theorem node_117_accepts : node_117.Accepts parameters box_117 := by
  norm_num [Tree.Accepts, node_117, box_117, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_118 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (1151 / 3072 : ℚ), (3 / 8 : ℚ)⟩
private def node_118 : Tree := .leaf .projection
private theorem node_118_accepts : node_118.Accepts parameters box_118 := by
  norm_num [Tree.Accepts, node_118, box_118, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_116 : Rectangle := ⟨(365 / 1024 : ℚ), (137 / 384 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_116 : Tree := .splitD (1151 / 3072 : ℚ) node_117 node_118
private theorem node_116_accepts : node_116.Accepts parameters box_116 := by
  change SplitDValid box_116 (1151 / 3072 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_116], node_117_accepts, node_118_accepts⟩

private def box_112 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (575 / 1536 : ℚ), (3 / 8 : ℚ)⟩
private def node_112 : Tree := .splitC (365 / 1024 : ℚ) node_113 node_116
private theorem node_112_accepts : node_112.Accepts parameters box_112 := by
  change SplitCValid box_112 (365 / 1024 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_112], node_113_accepts, node_116_accepts⟩

private def box_104 : Rectangle := ⟨(547 / 1536 : ℚ), (137 / 384 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_104 : Tree := .splitD (575 / 1536 : ℚ) node_105 node_112
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  change SplitDValid box_104 (575 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_104], node_105_accepts, node_112_accepts⟩

private def box_88 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (287 / 768 : ℚ), (3 / 8 : ℚ)⟩
private def node_88 : Tree := .splitC (547 / 1536 : ℚ) node_89 node_104
private theorem node_88_accepts : node_88.Accepts parameters box_88 := by
  change SplitCValid box_88 (547 / 1536 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_88], node_89_accepts, node_104_accepts⟩

private def box_58 : Rectangle := ⟨(91 / 256 : ℚ), (137 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_58 : Tree := .splitD (287 / 768 : ℚ) node_59 node_88
private theorem node_58_accepts : node_58.Accepts parameters box_58 := by
  change SplitDValid box_58 (287 / 768 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_58], node_59_accepts, node_88_accepts⟩

private def box_0 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_0 : Tree := .splitC (91 / 256 : ℚ) node_1 node_58
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (91 / 256 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_58_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C011
