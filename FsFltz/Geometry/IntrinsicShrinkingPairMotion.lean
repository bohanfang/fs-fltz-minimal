import FsFltz.Geometry.CompletionCollarExtension
import FsFltz.Geometry.CompletionDynamics
import FsFltz.Geometry.PairFamilyConstruction
import FsFltz.Geometry.DomainCompletionRestriction
import FsFltz.Geometry.FlowBridge
import FsFltz.Geometry.IntrinsicShrinkingPairScaling

/-!
# The actual intrinsic shrinking maps on a common open extension

Source: `geometric-part-fsf-proof.tex`, `lem:shrinking`, lines 470–488,
and `subsec:junction`, lines 1876–1892. A specified completion supplies
the negative flow and its unique native representative. The common open
space-time neighborhood is constructed by compactness, not assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CompleteLiouvilleFlow

/-- The actual time map of the specified smooth complete flow is a diffeomorphism. -/
def timeDiffeomorph {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x} (F : CompleteLiouvilleFlow M Z) (t : ℝ) :
    M.SmoothEquiv M where
  __ := (F.flow.toHomeomorph t).toEquiv
  contMDiff_toFun := F.smooth_action.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := F.smooth_action.comp (contMDiff_const.prodMk contMDiff_id)

end CompleteLiouvilleFlow

/-- Cartan's formula for this very completed flow gives the full primitive
pullback equation, at every positive or negative real time. -/
theorem CompleteLiouvilleManifold.pullback_timeDiffeomorph {d : ℕ}
    (X : CompleteLiouvilleManifold d) (t : ℝ) :
    X.manifold.pullback X.manifold (X.completeFlow.timeDiffeomorph t) X.primitive =
      Real.exp t • X.primitive := by
  funext x
  have h := LiouvilleFlowPrimitive.pullback_slice_eq_exp_smul
    X.manifold X.manifold X.primitive X.smooth_primitive X.field
    X.contraction (fun p => X.completeFlow.flow p.1 p.2) X.completeFlow.smooth_action
    (J := univ) (V := univ) isOpen_univ isPreconnected_univ isOpen_univ
    (fun y _ s _ => X.completeFlow.isMIntegralCurve y s)
    (t := t) (t₀ := 0) (x := x) (mem_univ _) (mem_univ _) (mem_univ _)
  simp only [sub_zero, Flow.map_zero_apply] at h
  change X.manifold.pullback X.manifold (fun y => X.completeFlow.flow t y) X.primitive x =
    Real.exp t • X.manifold.pullback X.manifold id X.primitive x at h
  rw [X.manifold.pullback_id] at h
  exact h

namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- Compactness gives a genuine two-sided time neighborhood and a single
open extension on which every finite shrinking map lifts through inclusion. -/
theorem exists_shrinking_neighborhood (T : ℝ) (hT : 0 ≤ T) :
    ∃ (J : TopologicalSpace.Opens ℝ)
      (U : TopologicalSpace.Opens D.domain.extension.Point),
      parameterInterval ⊆ J ∧ D.domain.carrier ⊆ U ∧
      ∀ t ∈ J, ∀ x ∈ U,
        C.ambient.completeFlow.flow (-(T * t)) (C.inclusion.map x) ∈ C.inclusionImage := by
  let f : ℝ × D.domain.extension.Point → C.ambient.manifold.Point :=
    fun p => C.ambient.completeFlow.flow (-(T * p.1)) (C.inclusion.map p.2)
  have hf : Continuous f := C.ambient.completeFlow.smooth_action.continuous.comp
    ((continuous_const.mul continuous_fst).neg.prodMk
      (C.inclusion.map.contMDiff.continuous.comp continuous_snd))
  have hcover : parameterInterval ×ˢ D.domain.carrier ⊆ f ⁻¹' C.inclusionImage := by
    intro p hp
    obtain ⟨y, _, hy⟩ := C.negative_flow_mem
      (show C.inclusion.map p.2 ∈ C.inclusion.map '' D.domain.carrier from ⟨p.2, hp.2, rfl⟩)
      (mul_nonneg hT hp.1.1)
    exact ⟨y, hy⟩
  obtain ⟨J, U, hJ, hU, hIJ, hDU, htube⟩ := generalized_tube_lemma
    (show IsCompact parameterInterval from isCompact_Icc) D.domain.compact
    (C.inclusionImage.isOpen.preimage hf) hcover
  exact ⟨⟨J, hJ⟩, ⟨U, hU⟩, hIJ, hDU, fun t ht x hx => htube (a := (t, x)) ⟨ht, hx⟩⟩

/-- The finite intrinsic flow, lifted through the actual compact inclusion
on its open image; outside that open image the auxiliary map is identity. -/
def shrinkingLift (T : ℝ) (t : ℝ) (x : D.domain.extension.Point) :
    D.domain.extension.Point :=
  if h : C.ambient.completeFlow.flow (-(T * t)) (C.inclusion.map x) ∈ C.inclusionImage
  then C.inclusionCoordinates ⟨C.ambient.completeFlow.flow (-(T * t)) (C.inclusion.map x), h⟩
  else x

theorem inclusion_shrinkingLift (T t : ℝ) (x : D.domain.extension.Point)
    (h : C.ambient.completeFlow.flow (-(T * t)) (C.inclusion.map x) ∈ C.inclusionImage) :
    C.inclusion.map (C.shrinkingLift T t x) =
      C.ambient.completeFlow.flow (-(T * t)) (C.inclusion.map x) := by
  simp only [shrinkingLift, dite_eq_left h, inclusionMap_inclusionCoordinates]

@[simp] theorem shrinkingLift_zero (T : ℝ) (x : D.domain.extension.Point) :
    C.shrinkingLift T 0 x = x := by
  have h : C.ambient.completeFlow.flow (-(T * 0)) (C.inclusion.map x) ∈ C.inclusionImage := by
    simp only [mul_zero, neg_zero, Flow.map_zero_apply]
    exact ⟨x, rfl⟩
  apply C.inclusion.embedding.injective
  rw [C.inclusion_shrinkingLift T 0 x h]
  simp

theorem shrinkingLift_mem_carrier (T : ℝ) (hT : 0 ≤ T) (t : Parameter)
    (x : D.domain.extension.Point) (hx : x ∈ D.domain.carrier) :
    C.shrinkingLift T t.val x ∈ D.domain.carrier := by
  obtain ⟨y, hy, he⟩ := C.negative_flow_mem
    (show C.inclusion.map x ∈ C.inclusion.map '' D.domain.carrier from ⟨x, hx, rfl⟩)
    (mul_nonneg hT t.property.1)
  have h : C.ambient.completeFlow.flow (-(T * t.val)) (C.inclusion.map x) ∈ C.inclusionImage :=
    ⟨y, he⟩
  have eq := C.inclusion.embedding.injective
    ((C.inclusion_shrinkingLift T t.val x h).trans he.symm)
  exact eq ▸ hy

/-- On any open set where the lifted flow is defined, its actual native
formula is jointly smooth at every derivative order. -/
theorem contMDiffOn_shrinkingLift (T : ℝ)
    (V : TopologicalSpace.Opens (ℝ × D.domain.extension.Point))
    (hdefined : ∀ p ∈ V,
      C.ambient.completeFlow.flow (-(T * p.1)) (C.inclusion.map p.2) ∈ C.inclusionImage) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => C.shrinkingLift T p.1 p.2) V := by
  let f : ℝ × D.domain.extension.Point → C.ambient.manifold.Point :=
    fun p => C.ambient.completeFlow.flow (-(T * p.1)) (C.inclusion.map p.2)
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ f :=
    C.ambient.completeFlow.smooth_action.comp
      ((contMDiff_const.mul contMDiff_fst).neg.prodMk
        (C.inclusion.map.contMDiff.comp contMDiff_snd))
  let g : V → C.inclusionImage := fun p => ⟨f p.val, hdefined p.val p.property⟩
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ g :=
    (ContMDiff.subtypeVal_comp_iff C.inclusionImage g).mp
      (hf.comp contMDiff_subtype_val)
  have hs := C.contMDiff_inclusionCoordinates.comp hg
  intro p hp
  have he : (fun q : V => C.shrinkingLift T q.val.1 q.val.2) =
      C.inclusionCoordinates ∘ g := by
    funext q
    simp only [shrinkingLift, dite_eq_left (hdefined q.val q.property)]
    rfl
  have hsub : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun q : V => C.shrinkingLift T q.val.1 q.val.2) ⟨p, hp⟩ := by
    rw [he]
    exact hs.contMDiffAt
  exact ((contMDiffAt_subtype_iff (x := (⟨p, hp⟩ : V))).mp hsub).contMDiffWithinAt

/-- The lifted intrinsic negative flow is an actual smooth family of maps
on the single constructed open ribbon extension. -/
theorem isSmoothInterval_shrinkingLift (T : ℝ)
    (J : TopologicalSpace.Opens ℝ) (U : TopologicalSpace.Opens D.domain.extension.Point)
    (hJ : parameterInterval ⊆ J)
    (hdefined : ∀ t ∈ J, ∀ x ∈ U,
      C.ambient.completeFlow.flow (-(T * t)) (C.inclusion.map x) ∈ C.inclusionImage) :
    (D.domain.extension.restrict U).IsSmoothIntervalMapFamily D.domain.extension
      (fun t x => C.shrinkingLift T t.val x.val) := by
  let V : TopologicalSpace.Opens (ℝ × D.domain.extension.Point) :=
    ⟨(J : Set ℝ) ×ˢ U, J.isOpen.prod U.isOpen⟩
  have hs := C.contMDiffOn_shrinkingLift T V (fun p hp => hdefined _ hp.1 _ hp.2)
  refine ⟨fun t x => C.shrinkingLift T t x.val, ?_, fun _ => rfl⟩
  refine ⟨(J : Set ℝ) ×ˢ univ, J.isOpen.prod isOpen_univ, ?_, ?_⟩
  · intro p hp
    exact ⟨hJ hp.1, mem_univ _⟩
  · exact hs.comp
      (contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)).contMDiffOn
      (fun p hp => ⟨hp.1, p.2.property⟩)

/-- Each lifted time map is an embedding with the actual injective native differential. -/
def shrinkingEmbedding (T : ℝ)
    (J : TopologicalSpace.Opens ℝ) (U : TopologicalSpace.Opens D.domain.extension.Point)
    (hJ : parameterInterval ⊆ J)
    (hdefined : ∀ t ∈ J, ∀ x ∈ U,
      C.ambient.completeFlow.flow (-(T * t)) (C.inclusion.map x) ∈ C.inclusionImage)
    (t : Parameter) : (D.domain.extension.restrict U).SmoothEmbedding D.domain.extension := by
  let f : U → D.domain.extension.Point := fun x => C.shrinkingLift T t.val x.val
  let V : TopologicalSpace.Opens (ℝ × D.domain.extension.Point) :=
    ⟨(J : Set ℝ) ×ˢ U, J.isOpen.prod U.isOpen⟩
  have hs := C.contMDiffOn_shrinkingLift T V (fun p hp => hdefined _ hp.1 _ hp.2)
  have hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ f := by
    intro x
    exact (hs.contMDiffAt (V.isOpen.mem_nhds
      (show (t.val, x.val) ∈ V from ⟨hJ t.property, x.property⟩))).comp x
      ((contMDiff_const.prodMk contMDiff_subtype_val).contMDiffAt)
  let g := C.ambient.completeFlow.timeDiffeomorph (-(T * t.val))
  have he : C.inclusion.map ∘ f = g ∘ C.inclusion.map ∘ (Subtype.val : U → D.domain.extension.Point) := by
    funext x
    exact C.inclusion_shrinkingLift T t.val x.val (hdefined _ (hJ t.property) _ x.property)
  have hcomp : Topology.IsEmbedding (C.inclusion.map ∘ f) := by
    rw [he]
    exact (g.toHomeomorph.isEmbedding.comp C.inclusion.embedding).comp Topology.IsEmbedding.subtypeVal
  have himm (x : U) : Function.Injective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (C.inclusion.map ∘ f) x) := by
    rw [he, mfderiv_comp x (g.contMDiff.mdifferentiableAt (by simp))
      ((C.inclusion.map.contMDiff.comp contMDiff_subtype_val).mdifferentiableAt (by simp))]
    erw [D.domain.extension.mfderiv_comp_restrict_val C.ambient.manifold U x
      (C.inclusion.map.contMDiff.mdifferentiableAt (by simp))]
    exact (g.mfderivToContinuousLinearEquiv (by simp) _).injective.comp (C.inclusion.immersion x.val)
  refine ⟨⟨f, hf⟩, C.inclusion.embedding.of_comp_iff.mp hcomp, ?_⟩
  intro x
  have hc := mfderiv_comp (f := f) (g := C.inclusion.map) x
    (C.inclusion.map.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  intro v w hvw
  apply himm x
  rw [hc]
  exact congrArg (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map (f x)) hvw

/-- The moving primitive is derived from the completed-flow equation and
carrier-only primitive preservation of inclusion. -/
theorem pullback_shrinkingEmbedding (T : ℝ) (hT : 0 ≤ T)
    (J : TopologicalSpace.Opens ℝ) (U : TopologicalSpace.Opens D.domain.extension.Point)
    (hJ : parameterInterval ⊆ J)
    (hdefined : ∀ t ∈ J, ∀ x ∈ U,
      C.ambient.completeFlow.flow (-(T * t)) (C.inclusion.map x) ∈ C.inclusionImage)
    (t : Parameter) (x : U) (hx : x.val ∈ D.domain.carrier) :
    (D.domain.extension.restrict U).pullback D.domain.extension
      (C.shrinkingEmbedding T J U hJ hdefined t).map D.liouville.primitive x =
      Real.exp (-(T * t.val)) • D.liouville.primitive x.val := by
  let R := D.domain.extension.restrict U
  let q := C.shrinkingEmbedding T J U hJ hdefined t
  let i := C.inclusion.comp (D.domain.extension.restrictInclusion U)
  let g := C.ambient.completeFlow.timeDiffeomorph (-(T * t.val))
  have he : C.inclusion.map ∘ q.map = g ∘ i.map := by
    funext y
    exact C.inclusion_shrinkingLift T t.val y.val (hdefined _ (hJ t.property) _ y.property)
  have hp : R.pullback C.ambient.manifold (C.inclusion.map ∘ q.map) C.ambient.primitive x =
      R.pullback D.domain.extension q.map D.liouville.primitive x := by
    rw [R.pullback_comp D.domain.extension C.ambient.manifold
      (q.map.contMDiff.mdifferentiable (by simp))
      (C.inclusion.map.contMDiff.mdifferentiable (by simp))]
    change (D.domain.extension.pullback C.ambient.manifold C.inclusion.map C.ambient.primitive
      (q.map x)).compContinuousLinearMap (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) q.map x) =
      (D.liouville.primitive (q.map x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) q.map x)
    have hqmem : q.map x ∈ D.domain.carrier := C.shrinkingLift_mem_carrier T hT t x.val hx
    rw [C.primitive_on_domain (q.map x) hqmem]
  rw [← hp, he, R.pullback_comp C.ambient.manifold C.ambient.manifold
    (i.map.contMDiff.mdifferentiable (by simp)) (g.contMDiff.mdifferentiable (by simp)),
    C.ambient.pullback_timeDiffeomorph]
  have hi : R.pullback C.ambient.manifold i.map C.ambient.primitive x = D.liouville.primitive x.val := by
    exact (D.domain.extension.pullback_comp_restrict_val C.ambient.manifold U
      C.inclusion.map C.ambient.primitive x).trans (C.primitive_on_domain x.val hx)
  ext vs
  exact congrArg (fun η => Real.exp (-(T * t.val)) * η vs) hi

end Completion
end FsFltz.Geometry
