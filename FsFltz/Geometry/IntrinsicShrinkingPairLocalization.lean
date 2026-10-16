import FsFltz.Geometry.IntrinsicShrinkingPairFamily

/-!
# Localization of the intrinsic shrinking source

The open extension required for joint smoothness does not replace the retained
compact pair silently. The identity on its compact ribbon is a scale-one
completion identification, with identity on the completed ambient.
Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomain
variable {d : ℕ} (D : CompactDomain d)
    (U : TopologicalSpace.Opens D.extension.Point) (hU : D.carrier ⊆ U) (x₀ : U)

/-- Total extension of the identity into an open neighborhood. Its values
outside that neighborhood do not enter any compact-domain assertion. -/
def restrictMap (x : D.extension.Point) : U :=
  if hx : x ∈ U then ⟨x, hx⟩ else x₀

theorem restrictMap_comp_val : D.restrictMap U x₀ ∘ Subtype.val = id := by
  funext x
  change (if hx : x.val ∈ U then (⟨x.val, hx⟩ : U) else x₀) = x
  rw [dite_eq_left x.property]

theorem contMDiffAt_restrictMap (x : D.extension.Point) (hx : x ∈ U) :
    ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) ∞ (D.restrictMap U x₀) x := by
  apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
  change ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) ∞
    (D.restrictMap U x₀ ∘ Subtype.val) (⟨x, hx⟩ : U)
  rw [D.restrictMap_comp_val U x₀]
  exact contMDiffAt_id

theorem mfderiv_restrictMap (x : D.extension.Point) (hx : x ∈ U) :
    mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (D.restrictMap U x₀) x =
      ContinuousLinearMap.id ℝ (Model d) := by
  have hc := mfderiv_comp (f := (Subtype.val : U → D.extension.Point))
    (g := D.restrictMap U x₀) (⟨x, hx⟩ : U)
    ((D.contMDiffAt_restrictMap U x₀ x hx).mdifferentiableAt (by simp))
    ((_root_.contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
  rw [D.restrictMap_comp_val U x₀, mfderiv_id, D.extension.mfderiv_restrict_val] at hc
  change ContinuousLinearMap.id ℝ (Model d) =
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (D.restrictMap U x₀) x).comp
      (ContinuousLinearMap.id ℝ (Model d)) at hc
  simpa using hc.symm

/-- Restricting an open extension is a genuine compact-domain relabeling. -/
def restrictOpen : CompactDomainDiffeomorph D (D.restrict U hU) where
  map := D.restrictMap U x₀
  inverse := Subtype.val
  sourceNeighbourhood := U
  targetNeighbourhood := univ
  open_source := U.isOpen
  open_target := isOpen_univ
  contains_source := hU
  contains_target := subset_univ _
  smooth_map := fun x hx => (D.contMDiffAt_restrictMap U x₀ x hx).contMDiffWithinAt
  smooth_inverse := (_root_.contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).contMDiffOn
  maps_source := by
    intro x hx
    change (D.restrictMap U x₀ x).val ∈ D.carrier
    have hxu : x ∈ U := hU hx
    rw [restrictMap, dite_eq_left hxu]
    exact hx
  maps_target := fun _ hx => hx
  left_inverse := by
    intro x hx
    have hxu : x ∈ U := hU hx
    rw [restrictMap, dite_eq_left hxu]
  right_inverse := by
    intro x _
    change D.restrictMap U x₀ x.val = x
    rw [restrictMap, dite_eq_left x.property]
  immersion := by
    intro x hx
    rw [D.mfderiv_restrictMap U x₀ x (hU hx)]
    exact Function.injective_id

end CompactDomain

namespace WitnessedPair
variable {n : ℕ} (P : WitnessedPair n)
    (U : TopologicalSpace.Opens P.ribbonDomain.domain.extension.Point)
    (hU : P.ribbonDomain.domain.carrier ⊆ U) (x₀ : U)
    (T : ℝ) (hT : 0 ≤ T) (J : TopologicalSpace.Opens ℝ)
    (hJ : parameterInterval ⊆ J)
    (hdefined : ∀ t ∈ J, ∀ x ∈ U,
      P.ribbonCompletion.ambient.completeFlow.flow (-(T * t))
        (P.ribbonCompletion.inclusion.map x) ∈ P.ribbonCompletion.inclusionImage)

/-- The literal retained pair is related to the constructed family's source
by an explicit permitted scale-one identification. -/
def shrinkingSourceIdentification : CompletionIdentification P
    (P.shrinkingDeformation U hU T hT J hJ hdefined).source where
  ambientEquiv := Diffeomorph.refl _ _ ∞
  primitive := P.ambientManifold.pullback_id _
  boundaryEquiv := Diffeomorph.refl _ _ ∞
  shift := fun _ => 0
  smooth_shift := contMDiff_const
  induced_at_infinity := fun x => ⟨0, fun r _ => by
    change P.ambientCompletion.endMap (x, r) = P.ambientCompletion.endMap (x, r + 0)
    rw [add_zero]⟩
  boundary_primitive := by
    change P.ambientDomain.domain.boundary.pullback _ id
      (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) = _
    rw [P.ambientDomain.domain.boundary.pullback_id]
    change P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive =
      fun x => Real.exp (-0) • P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x
    simp
  ribbonEquiv := P.ribbonDomain.domain.restrictOpen U hU x₀
  scale := 1
  positive_scale := zero_lt_one
  ribbon_primitive := by
    intro x hx
    let f := P.ribbonDomain.domain.restrictMap U x₀
    change (((P.shrinkingDeformation U hU T hT J hJ hdefined).pair parameterZero).ribbonDomain.liouville.primitive (f x)).compContinuousLinearMap
      (mfderiv (𝓘(ℝ, Model (2 * n - 2))) (𝓘(ℝ, Model (2 * n - 2))) f x) =
        1 • P.ribbonDomain.liouville.primitive x
    rw [P.shrinkingDeformation_primitive U hU T hT J hJ hdefined]
    have hd := P.ribbonDomain.domain.mfderiv_restrictMap U x₀ x (hU hx)
    rw [show mfderiv (𝓘(ℝ, Model (2 * n - 2)))
      (𝓘(ℝ, Model (2 * n - 2))) f x = ContinuousLinearMap.id ℝ (Model (2 * n - 2))
        from hd]
    have hv : (f x).val = x :=
      (P.ribbonDomain.domain.restrictOpen U hU x₀).left_inverse x hx
    rw [hv]
    simp only [parameterZero, mul_zero, neg_zero, Real.exp_zero, one_smul]
    ext vs
    rfl
  ribbon_square := by
    intro x hx
    change P.ribbonEmbedding.map x = P.ribbonEmbedding.map
      (P.ribbonCompletion.shrinkingLift T parameterZero.val
        (P.ribbonDomain.domain.restrictMap U x₀ x).val)
    rw [show parameterZero.val = 0 from rfl,
      P.ribbonCompletion.shrinkingLift_zero]
    exact congrArg P.ribbonEmbedding.map
      ((P.ribbonDomain.domain.restrictOpen U hU x₀).left_inverse x hx).symm

/-- A genuine finite comparison from the retained pair to the whole shrinking
endpoint: first the explicit source localization, then the constructed family. -/
def shrinkingChain : ComparisonChain P
    (P.shrinkingDeformation U hU T hT J hJ hdefined).target :=
  Quiver.Path.cons
    (Quiver.Path.cons Quiver.Path.nil
      (ComparisonStep.identification
        (P.shrinkingSourceIdentification U hU x₀ T hT J hJ hdefined)))
    (ComparisonStep.deformation (P.shrinkingDeformation U hU T hT J hJ hdefined))

/-- The source localization lifts the same ambient datum by the constant
homotopy, since its actual completed-ambient equivalence is identity. -/
def gradedShrinkingSourceIdentification (datum : P.Maslov) :
    GradedCompletionIdentification
      (P.shrinkingSourceIdentification U hU x₀ T hT J hJ hdefined) datum datum where
  family := (MaslovHomotopy.refl datum).family
  sourceJ := rfl
  targetJ := (pullbackAlmostComplex_refl P.ambientManifold datum.J).symm
  sourceSection := rfl
  targetSection := (pullbackSquaredTensor_refl P.ambientManifold datum.tensor).symm

/-- Ambient grading is carried by the exact constructed two-arrow comparison. -/
def gradedShrinkingChain (datum : P.Maslov) :
    GradedComparisonChain P (P.shrinkingChain U hU x₀ T hT J hJ hdefined) datum datum :=
  ((GradedComparisonChain.nil datum).cons
    (.identification (P.gradedShrinkingSourceIdentification U hU x₀ T hT J hJ hdefined datum))).cons
    (.deformation (P.gradedShrinkingDeformation U hU T hT J hJ hdefined datum))

end WitnessedPair
end FsFltz.Geometry
