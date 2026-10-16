import FsFltz.Geometry.IntrinsicBundleLocalCompletionOverlap
import FsFltz.Geometry.IntrinsicNativeEndpointPresentation
import FsFltz.Geometry.PrescribedFamilyCollarGerms

/-!
# Original local completions compared with retained global endpoints

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. The actual compact bundle coordinate change
extends from the retained local completion to an independently fixed
completion in a compatible chart. Primitive covariance and the original
transition germs construct the strict map; its compact inverse, boundary
orbits and all real flow times are preserved. The endpoint adapter uses
the existing pair deformation's exact compact domain and completion.

These are foundational comparison maps for supplied geometric families.
They do not assert existence of the target's finite chain, core equality
or prescribed grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

/-- Produced comparison with a retained completion in a compatible chart.
The original compact coordinate change is part of the conclusion. -/
structure CompatibleSliceComparison (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (B : NativeLiouvillePresentation (P.formInTrivialization g s))
    (C : Completion B.domain) where
  equiv : (F.sliceCompletion L s).ambient.manifold.SmoothEquiv C.ambient.manifold
  boundary : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv B.domain.domain.boundary
  primitive : (F.sliceCompletion L s).ambient.manifold.pullback C.ambient.manifold equiv
    C.ambient.primitive = (F.sliceCompletion L s).ambient.primitive
  compact : ∀ x, equiv (original (F.native.patches s) x) =
    C.inclusion.map (B.inclusion (c.val.coordChange g s x))
  compact_inverse : ∀ x, equiv.symm (C.inclusion.map (B.inclusion x)) =
    original (F.native.patches s) (g.coordChange c.val s x)
  boundary_square : ∀ b, equiv (original (F.native.patches s) b.val) =
    C.inclusion.map (B.domain.domain.boundaryInclusion.map (boundary b))
  end_square : ∀ b r, equiv ((F.sliceCompletion L s).endMap (b, r)) =
    C.endMap (boundary b, r)
  flow : ∀ x r, equiv ((F.sliceCompletion L s).ambient.completeFlow.flow r x) =
    C.ambient.completeFlow.flow r (equiv x)

/-- Original transition germs and primitive covariance extend to the two
fixed completions. Neither completion nor endpoint is replaced. -/
def compatibleSliceComparison (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base)
    (B : NativeLiouvillePresentation (P.formInTrivialization g s))
    (C : Completion B.domain) : CompatibleSliceComparison F L g s B C := by
  exact Classical.choice (show Nonempty (CompatibleSliceComparison F L g s B C) from by
    have hparam : s ∈ c.val.baseSet ∩ g.baseSet :=
      ⟨F.base_subset hs, by rw [hbase]; exact mem_univ s⟩
    let hec := compatibleTrivialization_of_mem c.property
    let h := transitionDiffeomorphOfCompatible c.val g hec hg hparam
    have hgerm : IsLocallyExtendibleNativeMap (k := k) h :=
      (hec.hasSmoothTransition hg).native_slice (hg.hasSmoothTransition hg) hparam
    have hcov := P.formInTrivialization_covariance c.val g hec hg hparam
    rw [P.formInTrivialization_eq_original c.val c.property hparam.1] at hcov
    have hprim (x : M) : (P.formInTrivialization g s (h x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = P.form c (F.reparam s) x := by
      rw [F.reparam_eq s hs]
      exact (congrFun hcov x).symm
    obtain ⟨e, b, hp, hc, hi, hb, _⟩ :=
      (F.sliceNativePresentation L s).exists_strictCompletionEquiv_of_nativeDiffeomorph
        B h hgerm hprim (F.sliceCompletion L s) C
    have hflow := (F.sliceCompletion L s).ambient.map_flow C.ambient e hp
    have hboundary (x : IntrinsicBoundary.Point k M) :
        e (original (F.native.patches s) x.val) =
          C.inclusion.map (B.domain.domain.boundaryInclusion.map (b x)) := by
      have hx := hb x
      change e ((compactDomain F.native.width_pos (F.native.collar s)
        (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
        (F.native.inverse s) (F.native.zero s)).boundaryInclusion.map x) = _ at hx
      rwa [compactDomain_boundaryInclusion] at hx
    refine ⟨⟨e, b, hp, hc, hi, hboundary, ?_, hflow⟩⟩
    intro x r
    rw [(F.sliceCompletion L s).end_flow, C.end_flow, hflow]
    congr 1
    exact hb x)

/-- The strict comparison is uniquely determined on the whole completion
by its original compact coordinate formula. -/
theorem CompatibleSliceComparison.equiv_unique (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (B : NativeLiouvillePresentation (P.formInTrivialization g s))
    (C : Completion B.domain) (a b : CompatibleSliceComparison F L g s B C) :
    a.equiv = b.equiv :=
  F.sliceCompletion_equiv_unique L s C.ambient a.equiv b.equiv a.primitive b.primitive
    (fun x => (a.compact x).trans (b.compact x).symm)

/-- The returned boundary map uses the literal native coordinate change,
as an equality in the original target compact extension. -/
theorem CompatibleSliceComparison.boundary_native (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (B : NativeLiouvillePresentation (P.formInTrivialization g s))
    (C : Completion B.domain) (a : CompatibleSliceComparison F L g s B C)
    (b : IntrinsicBoundary.Point k M) :
    B.domain.domain.boundaryInclusion.map (a.boundary b) =
      B.inclusion (c.val.coordChange g s b.val) := by
  apply C.inclusion.embedding.injective
  exact (a.boundary_square b).symm.trans (a.compact b.val)

/-- The full signed cylinder maps to the retained target boundary orbit.
This covers every outward radius and the original inward collar strip. -/
theorem CompatibleSliceComparison.map_cylinder (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (B : NativeLiouvillePresentation (P.formInTrivialization g s))
    (C : Completion B.domain) (a : CompatibleSliceComparison F L g s B C)
    (b : IntrinsicBoundary.Point k M) (r : ℝ) (hr : r < F.native.width) :
    a.equiv (cylinder (F.native.patches s) ⟨(r, b), hr, mem_univ _⟩) =
      C.endMap (a.boundary b, -r) := by
  rw [← F.sliceCompletion_end_cylinder L s b r hr, a.end_square]

/-- The returned boundary identification is forced by the actual native
bundle boundary transition and the target's retained native inclusion. -/
theorem CompatibleSliceComparison.boundary_eq_native (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base)
    (B : NativeLiouvillePresentation (P.formInTrivialization g s))
    (C : Completion B.domain) (a : CompatibleSliceComparison F L g s B C)
    (b : IntrinsicBoundary.Point k M) :
    a.boundary b = B.nativeBoundaryEquiv
      (compatibleBoundaryTransitionDiffeomorph c.val g
        (compatibleTrivialization_of_mem c.property) hg
        ⟨F.base_subset hs, by rw [hbase]; exact mem_univ s⟩ b) := by
  apply B.domain.domain.boundaryInclusion.embedding.injective
  rw [a.boundary_native F L g s B C, B.nativeBoundaryEquiv_inclusion,
    compatibleBoundaryTransitionDiffeomorph_val]

/-- Every signed cylinder point has the actual native boundary coordinate
change, followed by the target's fixed boundary presentation. -/
theorem CompatibleSliceComparison.map_cylinder_native (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base)
    (B : NativeLiouvillePresentation (P.formInTrivialization g s))
    (C : Completion B.domain) (a : CompatibleSliceComparison F L g s B C)
    (b : IntrinsicBoundary.Point k M) (r : ℝ) (hr : r < F.native.width) :
    a.equiv (cylinder (F.native.patches s) ⟨(r, b), hr, mem_univ _⟩) =
      C.endMap (B.nativeBoundaryEquiv
        (compatibleBoundaryTransitionDiffeomorph c.val g
          (compatibleTrivialization_of_mem c.property) hg
          ⟨F.base_subset hs, by rw [hbase]; exact mem_univ s⟩ b), -r) := by
  rw [a.map_cylinder F L g s B C b r hr, a.boundary_eq_native F L g hg hbase s hs B C]

/-- A dimension-flexible adapter on the original retained endpoint tuple.
All source and target inclusions are the specified native carrier maps. -/
structure EndpointSliceComparison (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) {d : ℕ} [NeZero d] (D : LiouvilleDomain d) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞) where
  equiv : (F.sliceCompletion L s).ambient.manifold.SmoothEquiv C.ambient.manifold
  boundary : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.domain.boundary
  primitive : (F.sliceCompletion L s).ambient.manifold.pullback C.ambient.manifold equiv
    C.ambient.primitive = (F.sliceCompletion L s).ambient.primitive
  compact : ∀ x, equiv (original (F.native.patches s) x) =
    C.inclusion.map (eM (c.val.coordChange g s x)).val
  compact_inverse : ∀ x, equiv.symm (C.inclusion.map (eM x).val) =
    original (F.native.patches s) (g.coordChange c.val s x)
  boundary_square : ∀ b, equiv (original (F.native.patches s) b.val) =
    C.inclusion.map (D.domain.boundaryInclusion.map (boundary b))
  end_square : ∀ b r, equiv ((F.sliceCompletion L s).endMap (b, r)) =
    C.endMap (boundary b, r)
  flow : ∀ x r, equiv ((F.sliceCompletion L s).ambient.completeFlow.flow r x) =
    C.ambient.completeFlow.flow r (equiv x)

/-- Package the endpoint's already produced primitive and coordinate laws
with `of_endpoint`, and extend the original coordinate change to its exact
retained completion. No replacement completion is constructed. -/
def endpointSliceComparison (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base) {d : ℕ} [NeZero d] (hdim : k + 1 = d)
    (D : LiouvilleDomain d) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (hp : ∀ x, (D.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) (fun y => (eM y).val) x) =
        P.formInTrivialization g s x)
    (hc : HasNativeCoordinateExtensions (k := k) D.domain.extension (fun x => (eM x).val)) :
    EndpointSliceComparison F L g s D C eM := by
  subst d
  let B := NativeLiouvillePresentation.of_endpoint (P.formInTrivialization g s) D eM hp hc
  let a := F.compatibleSliceComparison L g hg hbase s hs B C
  exact ⟨a.equiv, a.boundary, a.primitive, a.compact, a.compact_inverse,
    a.boundary_square, a.end_square, a.flow⟩

/-- Compact native boundary agreement forces the actual endpoint boundary
presentation composed with the original bundle transition. The supplied
boundary square is an existing endpoint law, never an extra completed map. -/
theorem EndpointSliceComparison.boundary_eq_native (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base) {d : ℕ} [NeZero d]
    (D : LiouvilleDomain d) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (eB : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.domain.boundary)
    (hb : ∀ b, D.domain.boundaryInclusion.map (eB b) = (eM b.val).val)
    (a : EndpointSliceComparison F L g s D C eM) (b : IntrinsicBoundary.Point k M) :
    a.boundary b = eB
      (compatibleBoundaryTransitionDiffeomorph c.val g
        (compatibleTrivialization_of_mem c.property) hg
        ⟨F.base_subset hs, by rw [hbase]; exact mem_univ s⟩ b) := by
  apply D.domain.boundaryInclusion.embedding.injective
  apply C.inclusion.embedding.injective
  rw [hb, compatibleBoundaryTransitionDiffeomorph_val]
  exact (a.boundary_square b).symm.trans (a.compact b.val)

/-- Uniqueness also applies to the exact pre-existing endpoint tuple. -/
theorem EndpointSliceComparison.equiv_unique (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) {d : ℕ} [NeZero d] (D : LiouvilleDomain d) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (a b : EndpointSliceComparison F L g s D C eM) : a.equiv = b.equiv :=
  F.sliceCompletion_equiv_unique L s C.ambient a.equiv b.equiv a.primitive b.primitive
    (fun x => (a.compact x).trans (b.compact x).symm)

/-- The endpoint boundary orbit keeps its original native boundary map on
the entire attached cylinder, including the inward strip. -/
theorem EndpointSliceComparison.map_cylinder_native (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base) {d : ℕ} [NeZero d]
    (D : LiouvilleDomain d) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (eB : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.domain.boundary)
    (hb : ∀ b, D.domain.boundaryInclusion.map (eB b) = (eM b.val).val)
    (a : EndpointSliceComparison F L g s D C eM)
    (b : IntrinsicBoundary.Point k M) (r : ℝ) (hr : r < F.native.width) :
    a.equiv (cylinder (F.native.patches s) ⟨(r, b), hr, mem_univ _⟩) =
      C.endMap (eB
        (compatibleBoundaryTransitionDiffeomorph c.val g
          (compatibleTrivialization_of_mem c.property) hg
          ⟨F.base_subset hs, by rw [hbase]; exact mem_univ s⟩ b), -r) := by
  rw [← F.sliceCompletion_end_cylinder L s b r hr, a.end_square,
    a.boundary_eq_native F L g hg hbase s hs D C eM eB hb]

variable {n : ℕ} [NeZero n]

/-- The ambient consumer instantiates `of_endpoint` on this exact pair
deformation's compact carrier and retained ambient completion. Its premises
are precisely the native endpoint laws already produced for that family. -/
def ambientEndpointSliceComparison (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base) (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
    (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair u).ambientDomain.domain.Point ∞)
    (hp : ∀ u x, ((Q.pair u).ambientDomain.liouville.primitive (eAs u x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs u y).val) x) =
        P.formInTrivialization g u x)
    (hc : ∀ u, HasNativeCoordinateExtensions (k := k)
      (Q.pair u).ambientDomain.domain.extension (fun x => (eAs u x).val)) :
    EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s) :=
  F.endpointSliceComparison L g hg hbase s hs hdim (Q.pair s).ambientDomain
    (Q.pair s).ambientCompletion (eAs s) (hp s) (hc s)

/-- Compose with the inverse of the same deformation's specified ambient
completion presentation, yielding its fixed source ambient. -/
def ambientSourceSliceEquiv (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (Q : PairDeformation n)
    (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair u).ambientDomain.domain.Point ∞)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s)) :
    (F.sliceCompletion L s).ambient.manifold.SmoothEquiv Q.source.ambientCompletion.ambient.manifold :=
  a.equiv.trans (Q.ambientCompletionPresentation s).equiv.symm

/-- The fixed-source comparison preserves the parameter-dependent completed
primitive of this very deformation, including at both parameter endpoints. -/
theorem ambientSourceSliceEquiv_primitive (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (Q : PairDeformation n)
    (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair u).ambientDomain.domain.Point ∞)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s)) :
    (F.sliceCompletion L s).ambient.manifold.pullback Q.source.ambientCompletion.ambient.manifold
      (F.ambientSourceSliceEquiv L g s Q eAs a) (Q.completedPrimitive s) =
        (F.sliceCompletion L s).ambient.primitive := by
  unfold ambientSourceSliceEquiv PairDeformation.completedPrimitive PairDeformation.source
  change (F.sliceCompletion L s).ambient.manifold.pullback
    (Q.pair parameterZero).ambientCompletion.ambient.manifold
    ((Q.ambientCompletionPresentation s).equiv.symm ∘ a.equiv) _ = _
  rw [(F.sliceCompletion L s).ambient.manifold.pullback_comp
    (Q.pair s).ambientCompletion.ambient.manifold
    (Q.pair parameterZero).ambientCompletion.ambient.manifold
    (a.equiv.mdifferentiable (by simp))
    ((Q.ambientCompletionPresentation s).equiv.symm.mdifferentiable (by simp)),
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.pullback_symm_pullback
      (Q.pair s).ambientCompletion.ambient.manifold
      (Q.ambientCompletionPresentation s).equiv (Q.pair s).ambientCompletion.ambient.primitive,
    a.primitive]

/-- The inverse comparison has the same parameter-dependent primitive. -/
theorem ambientSourceSliceEquiv_inverse_primitive (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (Q : PairDeformation n)
    (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair u).ambientDomain.domain.Point ∞)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s)) :
    Q.source.ambientCompletion.ambient.manifold.pullback (F.sliceCompletion L s).ambient.manifold
      (F.ambientSourceSliceEquiv L g s Q eAs a).symm
      (F.sliceCompletion L s).ambient.primitive = Q.completedPrimitive s := by
  rw [← F.ambientSourceSliceEquiv_primitive L g s Q eAs a]
  exact (F.sliceCompletion L s).ambient.manifold.pullback_symm_pullback
    Q.source.ambientCompletion.ambient.manifold
    (F.ambientSourceSliceEquiv L g s Q eAs a) (Q.completedPrimitive s)

/-- On every original compact point the map uses the same retained endpoint
carrier and the inverse of the same specified completion presentation. -/
theorem ambientSourceSliceEquiv_compact (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (Q : PairDeformation n)
    (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair u).ambientDomain.domain.Point ∞)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s)) (x : M) :
    F.ambientSourceSliceEquiv L g s Q eAs a (original (F.native.patches s) x) =
      (Q.ambientCompletionPresentation s).equiv.symm
        ((Q.pair s).ambientCompletion.inclusion.map (eAs s (c.val.coordChange g s x)).val) :=
  congrArg (Q.ambientCompletionPresentation s).equiv.symm (a.compact x)

/-- The inverse compact equation uses the original reverse coordinate
change on the same retained endpoint and completion presentation. -/
theorem ambientSourceSliceEquiv_compact_inverse (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (Q : PairDeformation n)
    (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair u).ambientDomain.domain.Point ∞)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s)) (x : M) :
    (F.ambientSourceSliceEquiv L g s Q eAs a).symm
      ((Q.ambientCompletionPresentation s).equiv.symm
        ((Q.pair s).ambientCompletion.inclusion.map (eAs s x).val)) =
      original (F.native.patches s) (g.coordChange c.val s x) := by
  change a.equiv.symm ((Q.ambientCompletionPresentation s).equiv
    ((Q.ambientCompletionPresentation s).equiv.symm _)) = _
  rw [(Q.ambientCompletionPresentation s).equiv.apply_symm_apply, a.compact_inverse]

/-- All real boundary orbits use the prescribed trajectory of the same
deformation's fixed source presentation. -/
theorem ambientSourceSliceEquiv_end (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (Q : PairDeformation n)
    (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair u).ambientDomain.domain.Point ∞)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s)) (b : IntrinsicBoundary.Point k M) (r : ℝ) :
    F.ambientSourceSliceEquiv L g s Q eAs a ((F.sliceCompletion L s).endMap (b, r)) =
      (Q.ambientCompletionPresentation s).prescribedEndMap
        ((Q.ambientPresentation s).boundaryEquiv.symm (a.boundary b), r) := by
  change (Q.ambientCompletionPresentation s).equiv.symm (a.equiv _) =
    (Q.ambientCompletionPresentation s).equiv.symm
      ((Q.pair s).ambientCompletion.endMap
        ((Q.ambientPresentation s).boundaryEquiv
          ((Q.ambientPresentation s).boundaryEquiv.symm (a.boundary b)), r))
  rw [a.end_square, (Q.ambientPresentation s).boundaryEquiv.apply_symm_apply]

/-- The full signed-cylinder formula uses the actual native bundle boundary
transition and the already produced boundary maps of this exact deformation. -/
theorem ambientSourceSliceEquiv_cylinder_native (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base) (Q : PairDeformation n)
    (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair u).ambientDomain.domain.Point ∞)
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s))
    (b : IntrinsicBoundary.Point k M) (r : ℝ) (hr : r < F.native.width) :
    F.ambientSourceSliceEquiv L g s Q eAs a
      (cylinder (F.native.patches s) ⟨(r, b), hr, mem_univ _⟩) =
      (Q.ambientCompletionPresentation s).prescribedEndMap
        ((Q.ambientPresentation s).boundaryEquiv.symm (eBs s
          (compatibleBoundaryTransitionDiffeomorph c.val g
            (compatibleTrivialization_of_mem c.property) hg
            ⟨F.base_subset hs, by rw [hbase]; exact mem_univ s⟩ b)), -r) := by
  rw [← F.sliceCompletion_end_cylinder L s b r hr,
    F.ambientSourceSliceEquiv_end L g s Q eAs a,
    a.boundary_eq_native F L g hg hbase s hs (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s) (eBs s) (hb s)]

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily
