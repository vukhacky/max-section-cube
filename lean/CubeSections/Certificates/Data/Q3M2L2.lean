import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q3M2L2

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨3, 2, 2⟩

private def box_4 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (127 / 512 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(1 / 4 : ℚ), (25 / 96 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_6 : Tree := .leaf (.strip (251 / 1024 : ℚ))
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  norm_num [Tree.Accepts, node_6, box_6, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_7 : Rectangle := ⟨(25 / 96 : ℚ), (13 / 48 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (69 / 256 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_5 : Tree := .splitC (25 / 96 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitCValid box_5 (25 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_3 : Tree := .splitD (13 / 48 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_10 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_10 : Tree := .leaf (.strip (131 / 512 : ℚ))
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_11 : Tree := .leaf (.strip (67 / 256 : ℚ))
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_9 : Tree := .splitC (9 / 32 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_13 : Rectangle := ⟨(13 / 48 : ℚ), (9 / 32 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_13 : Tree := .leaf .projection
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  norm_num [Tree.Accepts, node_13, box_13, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(9 / 32 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_12 : Tree := .splitC (9 / 32 : ℚ) node_13 node_14
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitCValid box_12 (9 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_12], node_13_accepts, node_14_accepts⟩

private def box_8 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_8 : Tree := .splitD (13 / 48 : ℚ) node_9 node_12
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  change SplitDValid box_8 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_8], node_9_accepts, node_12_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_2 : Tree := .splitC (13 / 48 : ℚ) node_3 node_8
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_8_accepts⟩

private def box_17 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (5 / 16 : ℚ)⟩
private def node_17 : Tree := .leaf .projection
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  norm_num [Tree.Accepts, node_17, box_17, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (5 / 16 : ℚ), (1 / 3 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(1 / 4 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_16 : Tree := .splitD (5 / 16 : ℚ) node_17 node_18
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_18_accepts⟩

private def box_19 : Rectangle := ⟨(13 / 48 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_15 : Tree := .splitC (13 / 48 : ℚ) node_16 node_19
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_19_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 4 : ℚ), (7 / 24 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_1 : Tree := .splitD (7 / 24 : ℚ) node_2 node_15
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_15_accepts⟩

private def box_23 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (13 / 48 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_24 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (13 / 48 : ℚ), (7 / 24 : ℚ)⟩
private def node_24 : Tree := .leaf .projection
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  norm_num [Tree.Accepts, node_24, box_24, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_22 : Rectangle := ⟨(7 / 24 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_22 : Tree := .splitD (13 / 48 : ℚ) node_23 node_24
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  change SplitDValid box_22 (13 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_22], node_23_accepts, node_24_accepts⟩

private def box_25 : Rectangle := ⟨(5 / 16 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_25 : Tree := .leaf .projection
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  norm_num [Tree.Accepts, node_25, box_25, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (7 / 24 : ℚ)⟩
private def node_21 : Tree := .splitC (5 / 16 : ℚ) node_22 node_25
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitCValid box_21 (5 / 16 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_21], node_22_accepts, node_25_accepts⟩

private def box_26 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (7 / 24 : ℚ), (1 / 3 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(7 / 24 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_20 : Tree := .splitD (7 / 24 : ℚ) node_21 node_26
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitDValid box_20 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_20], node_21_accepts, node_26_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 4 : ℚ), (1 / 3 : ℚ), (1 / 4 : ℚ), (1 / 3 : ℚ)⟩
private def node_0 : Tree := .splitC (7 / 24 : ℚ) node_1 node_20
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (7 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_20_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q3M2L2
