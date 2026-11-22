import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C059

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_4 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (13 / 32 : ℚ), (157 / 384 : ℚ)⟩
private def node_4 : Tree := .leaf .projection
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (157 / 384 : ℚ), (79 / 192 : ℚ)⟩
private def node_5 : Tree := .leaf .projection
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_3 : Tree := .splitD (157 / 384 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_7 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (13 / 32 : ℚ), (157 / 384 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (157 / 384 : ℚ), (79 / 192 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_6 : Tree := .splitD (157 / 384 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_2 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_2 : Tree := .splitC (47 / 128 : ℚ) node_3 node_6
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_6_accepts⟩

private def box_11 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (79 / 192 : ℚ), (53 / 128 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (53 / 128 : ℚ), (5 / 12 : ℚ)⟩
private def node_12 : Tree := .leaf .projection
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_10 : Tree := .splitD (53 / 128 : ℚ) node_11 node_12
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitDValid box_10 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_10], node_11_accepts, node_12_accepts⟩

private def box_14 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (79 / 192 : ℚ), (53 / 128 : ℚ)⟩
private def node_14 : Tree := .leaf .projection
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (53 / 128 : ℚ), (5 / 12 : ℚ)⟩
private def node_15 : Tree := .leaf .projection
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_13 : Tree := .splitD (53 / 128 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_9 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_9 : Tree := .splitC (47 / 128 : ℚ) node_10 node_13
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_13_accepts⟩

private def box_1 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_1 : Tree := .splitD (79 / 192 : ℚ) node_2 node_9
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_9_accepts⟩

private def box_19 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (13 / 32 : ℚ), (157 / 384 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (157 / 384 : ℚ), (79 / 192 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_18 : Tree := .splitD (157 / 384 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_22 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (157 / 384 : ℚ)⟩
private def node_22 : Tree := .leaf .projection
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_23 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (157 / 384 : ℚ), (79 / 192 : ℚ)⟩
private def node_23 : Tree := .leaf .projection
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  norm_num [Tree.Accepts, node_23, box_23, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_21 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_21 : Tree := .splitD (157 / 384 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (157 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_17 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (79 / 192 : ℚ)⟩
private def node_17 : Tree := .splitC (143 / 384 : ℚ) node_18 node_21
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitCValid box_17 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_17], node_18_accepts, node_21_accepts⟩

private def box_26 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (79 / 192 : ℚ), (53 / 128 : ℚ)⟩
private def node_26 : Tree := .leaf .projection
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  norm_num [Tree.Accepts, node_26, box_26, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_27 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (53 / 128 : ℚ), (5 / 12 : ℚ)⟩
private def node_27 : Tree := .leaf .projection
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  norm_num [Tree.Accepts, node_27, box_27, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_25 : Rectangle := ⟨(71 / 192 : ℚ), (143 / 384 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_25 : Tree := .splitD (53 / 128 : ℚ) node_26 node_27
private theorem node_25_accepts : node_25.Accepts parameters box_25 := by
  change SplitDValid box_25 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_25], node_26_accepts, node_27_accepts⟩

private def box_29 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (79 / 192 : ℚ), (53 / 128 : ℚ)⟩
private def node_29 : Tree := .leaf .projection
private theorem node_29_accepts : node_29.Accepts parameters box_29 := by
  norm_num [Tree.Accepts, node_29, box_29, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_30 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (53 / 128 : ℚ), (5 / 12 : ℚ)⟩
private def node_30 : Tree := .leaf .projection
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  norm_num [Tree.Accepts, node_30, box_30, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_28 : Rectangle := ⟨(143 / 384 : ℚ), (3 / 8 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_28 : Tree := .splitD (53 / 128 : ℚ) node_29 node_30
private theorem node_28_accepts : node_28.Accepts parameters box_28 := by
  change SplitDValid box_28 (53 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_28], node_29_accepts, node_30_accepts⟩

private def box_24 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (79 / 192 : ℚ), (5 / 12 : ℚ)⟩
private def node_24 : Tree := .splitC (143 / 384 : ℚ) node_25 node_28
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitCValid box_24 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_24], node_25_accepts, node_28_accepts⟩

private def box_16 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_16 : Tree := .splitD (79 / 192 : ℚ) node_17 node_24
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (79 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_24_accepts⟩

private def box_0 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_0 : Tree := .splitC (71 / 192 : ℚ) node_1 node_16
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_16_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C059
