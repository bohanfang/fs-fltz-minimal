import FsFltz.Geometry.MovingCompletionComparison
import FsFltz.Geometry.IntrinsicNativePairIdentification

/-!
# Completion coherence on the original native pairs

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. Independently prescribed pairs presenting the
same native compact ambient and full ribbon are compared on their original
completions. The ambient comparison comes from the native primitive and
inward collar. The original boundary inclusion and full ribbon squares
determine its boundary and ribbon compatibility.

These are conditional foundations for changes of presentation. They do not
construct a target-specific chain, marking, core equality or grading, or
assert joint smoothness of the constructed slice comparisons.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace IntrinsicLiouville

variable {a d : ℕ} [NeZero d] {A : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]

/-- Compare the original completions and retain the specified native
boundary maps. Their inclusion squares force these maps to be the native
boundary presentations; no ambient comparison or end square is input. -/
theorem exists_strictNativeComparison_with_boundary_square
    (hdim : a + 1 = d) (D E : LiouvilleDomain d)
    (C : Completion D) (K : Completion E)
    (lam : Form a A 1) (hlam : IsLocallyExtendibleForm lam)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative lam) x)
    (hout : ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector lam (exteriorDerivative lam) x.val)))
    (eA : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ d) A D.domain.Point ∞)
    (eA' : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ d) A E.domain.Point ∞)
    (hp : ∀ x, (D.liouville.primitive (eA x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model d) (fun y => (eA y).val) x) = lam x)
    (hp' : ∀ x, (E.liouville.primitive (eA' x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model d) (fun y => (eA' y).val) x) = lam x)
    (hc : HasNativeCoordinateExtensions (k := a) D.domain.extension (fun x => (eA x).val))
    (hc' : HasNativeCoordinateExtensions (k := a) E.domain.extension (fun x => (eA' x).val))
    (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv D.domain.boundary)
    (eB' : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv E.domain.boundary)
    (hB : ∀ x, D.domain.boundaryInclusion.map (eB x) = (eA x.val).val)
    (hB' : ∀ x, E.domain.boundaryInclusion.map (eB' x) = (eA' x.val).val) :
    ∃ f : C.ambient.manifold.SmoothEquiv K.ambient.manifold,
      C.ambient.manifold.pullback K.ambient.manifold f K.ambient.primitive =
        C.ambient.primitive ∧
      (∀ x, f (C.inclusion.map (eA x).val) = K.inclusion.map (eA' x).val) ∧
      (∀ x, f.symm (K.inclusion.map (eA' x).val) = C.inclusion.map (eA x).val) ∧
      (∀ x r, f (C.endMap (eB x, r)) = K.endMap (eB' x, r)) := by
  subst d
  let P := NativeLiouvillePresentation.of_endpoint lam D eA hp hc
  let Q := NativeLiouvillePresentation.of_endpoint lam E eA' hp' hc'
  have hBP (x : IntrinsicBoundary.Point a A) : eB x = P.nativeBoundaryEquiv x := by
    apply D.domain.boundaryInclusion.embedding.injective
    exact (hB x).trans (P.nativeBoundaryEquiv_inclusion x).symm
  have hBQ (x : IntrinsicBoundary.Point a A) : eB' x = Q.nativeBoundaryEquiv x := by
    apply E.domain.boundaryInclusion.embedding.injective
    exact (hB' x).trans (Q.nativeBoundaryEquiv_inclusion x).symm
  obtain ⟨f, hprimitive, hcompact, hinverse, hend⟩ :=
    exists_strictNativeSliceComparison lam hlam hnd hout P Q C K
  refine ⟨f, hprimitive, hcompact, hinverse, ?_⟩
  intro x r
  rw [hBP, hBQ]
  exact hend x r

end IntrinsicLiouville

namespace Completion

variable {d : ℕ} [NeZero d] {D E : LiouvilleDomain d}

/-- A strict completed comparison matching both original compact carriers
has a compact diffeomorphism on those original domains. Smoothness is
proved on the actual open images of the two compact inclusions. -/
theorem exists_compactDiffeomorph_of_native_squares
    {a : ℕ} {A : Type} [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
    (C : Completion D) (K : Completion E)
    (e : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ d) A D.domain.Point ∞)
    (e' : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ d) A E.domain.Point ∞)
    (f : C.ambient.manifold.SmoothEquiv K.ambient.manifold)
    (hs : ∀ x, f (C.inclusion.map (e x).val) = K.inclusion.map (e' x).val)
    (hi : ∀ x, f.symm (K.inclusion.map (e' x).val) = C.inclusion.map (e x).val) :
    ∃ g : CompactDomainDiffeomorph D.domain E.domain,
      (∀ x, g.map (e x).val = (e' x).val) ∧
      (∀ x, g.inverse (e' x).val = (e x).val) := by
  classical
  let U : TopologicalSpace.Opens D.domain.extension.Point :=
    ⟨(fun z => f (C.inclusion.map z)) ⁻¹' K.inclusionImage,
      K.inclusionImage.isOpen.preimage (f.continuous.comp C.inclusion.map.contMDiff.continuous)⟩
  let V : TopologicalSpace.Opens E.domain.extension.Point :=
    ⟨(fun z => f.symm (K.inclusion.map z)) ⁻¹' C.inclusionImage,
      C.inclusionImage.isOpen.preimage (f.symm.continuous.comp K.inclusion.map.contMDiff.continuous)⟩
  let q : U → K.inclusionImage := fun z => ⟨f (C.inclusion.map z.val), z.property⟩
  let q' : V → C.inclusionImage := fun z => ⟨f.symm (K.inclusion.map z.val), z.property⟩
  have hq : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ q :=
    (ContMDiff.subtypeVal_comp_iff K.inclusionImage q).mp
      ((f.contMDiff.comp C.inclusion.map.contMDiff).comp contMDiff_subtype_val)
  have hq' : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ q' :=
    (ContMDiff.subtypeVal_comp_iff C.inclusionImage q').mp
      ((f.symm.contMDiff.comp K.inclusion.map.contMDiff).comp contMDiff_subtype_val)
  let u : D.domain.extension.Point → E.domain.extension.Point := fun z =>
    if hz : z ∈ U then K.inclusionCoordinates (q ⟨z, hz⟩)
    else (e' (e.symm ⟨(C.carrier_nonempty_of_extension_nonempty ⟨z⟩).choose,
      (C.carrier_nonempty_of_extension_nonempty ⟨z⟩).choose_spec⟩)).val
  let v : E.domain.extension.Point → D.domain.extension.Point := fun z =>
    if hz : z ∈ V then C.inclusionCoordinates (q' ⟨z, hz⟩)
    else (e (e'.symm ⟨(K.carrier_nonempty_of_extension_nonempty ⟨z⟩).choose,
      (K.carrier_nonempty_of_extension_nonempty ⟨z⟩).choose_spec⟩)).val
  have hu (z : U) : u z.val = K.inclusionCoordinates (q z) := by
    dsimp only [u]
    rw [dite_eq_left z.property]
  have hv (z : V) : v z.val = C.inclusionCoordinates (q' z) := by
    dsimp only [v]
    rw [dite_eq_left z.property]
  have hus : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ u U := by
    intro z hz
    have h : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (fun w : U => u w.val) :=
      (K.contMDiff_inclusionCoordinates.comp hq).congr hu
    exact ((contMDiffAt_subtype_iff (f := u) (x := (⟨z, hz⟩ : U))).mp (h _)).contMDiffWithinAt
  have hvs : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ v V := by
    intro z hz
    have h : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (fun w : V => v w.val) :=
      (C.contMDiff_inclusionCoordinates.comp hq').congr hv
    exact ((contMDiffAt_subtype_iff (f := v) (x := (⟨z, hz⟩ : V))).mp (h _)).contMDiffWithinAt
  have heU (x : A) : (e x).val ∈ U := by
    change f (C.inclusion.map (e x).val) ∈ K.inclusionImage
    rw [hs]
    exact ⟨(e' x).val, rfl⟩
  have heV (x : A) : (e' x).val ∈ V := by
    change f.symm (K.inclusion.map (e' x).val) ∈ C.inclusionImage
    rw [hi]
    exact ⟨(e x).val, rfl⟩
  have hu_native (x : A) : u (e x).val = (e' x).val := by
    rw [hu ⟨(e x).val, heU x⟩]
    apply K.inclusion.embedding.injective
    exact (K.inclusionMap_inclusionCoordinates _).trans (hs x)
  have hv_native (x : A) : v (e' x).val = (e x).val := by
    rw [hv ⟨(e' x).val, heV x⟩]
    apply C.inclusion.embedding.injective
    exact (C.inclusionMap_inclusionCoordinates _).trans (hi x)
  have hcarrierU : D.domain.carrier ⊆ U := by
    intro z hz
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
    have hx' : (e x).val = z := congrArg Subtype.val hx
    exact hx' ▸ heU x
  have hcarrierV : E.domain.carrier ⊆ V := by
    intro z hz
    obtain ⟨x, hx⟩ := e'.surjective ⟨z, hz⟩
    have hx' : (e' x).val = z := congrArg Subtype.val hx
    exact hx' ▸ heV x
  let g : CompactDomainDiffeomorph D.domain E.domain :=
    { map := u
      inverse := v
      sourceNeighbourhood := U
      targetNeighbourhood := V
      open_source := U.isOpen
      open_target := V.isOpen
      contains_source := hcarrierU
      contains_target := hcarrierV
      smooth_map := hus
      smooth_inverse := hvs
      maps_source := by
        intro z hz
        obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
        have hx' : (e x).val = z := congrArg Subtype.val hx
        rw [← hx', hu_native]
        exact (e' x).property
      maps_target := by
        intro z hz
        obtain ⟨x, hx⟩ := e'.surjective ⟨z, hz⟩
        have hx' : (e' x).val = z := congrArg Subtype.val hx
        rw [← hx', hv_native]
        exact (e x).property
      left_inverse := by
        intro z hz
        obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
        have hx' : (e x).val = z := congrArg Subtype.val hx
        rw [← hx', hu_native, hv_native]
      right_inverse := by
        intro z hz
        obtain ⟨x, hx⟩ := e'.surjective ⟨z, hz⟩
        have hx' : (e' x).val = z := congrArg Subtype.val hx
        rw [← hx', hv_native, hu_native]
      immersion := by
        intro z hz
        have hzU := hcarrierU hz
        have heq : K.inclusion.map ∘ u =ᶠ[𝓝 z] f ∘ C.inclusion.map := by
          filter_upwards [U.isOpen.mem_nhds hzU] with y hy
          exact (congrArg K.inclusion.map (hu ⟨y, hy⟩)).trans
            (K.inclusionMap_inclusionCoordinates _)
        have hd := mfderiv_comp (f := u) (g := K.inclusion.map) z
          (K.inclusion.map.contMDiff.mdifferentiableAt (by simp))
          ((hus.contMDiffAt (U.isOpen.mem_nhds hzU)).mdifferentiableAt (by simp))
        rw [heq.mfderiv_eq] at hd
        have hd' := mfderiv_comp (f := C.inclusion.map) (g := f) z
          (f.contMDiff.mdifferentiableAt (by simp))
          (C.inclusion.map.contMDiff.mdifferentiableAt (by simp))
        rw [hd'] at hd
        have hinj := (f.isInvertible_mfderiv (x := C.inclusion.map z) (by simp)).injective.comp
          (C.inclusion.immersion z)
        have hcast := (tangentSpaceCast 𝓘(ℝ, Model d)
          ((f ∘ C.inclusion.map) z) ((K.inclusion.map ∘ u) z)).injective.comp hinj
        change Function.Injective ((tangentSpaceCast 𝓘(ℝ, Model d)
          ((f ∘ C.inclusion.map) z) ((K.inclusion.map ∘ u) z)).toContinuousLinearMap.comp
            ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f (C.inclusion.map z)).comp
              (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map z))) at hcast
        rw [hd] at hcast
        intro v w hvw
        apply hcast
        exact congrArg (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) K.inclusion.map (u z)) hvw }
  exact ⟨g, hu_native, hv_native⟩

end Completion

namespace IntrinsicLiouville

variable {k d : ℕ} [NeZero d] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The same native primitive constructs the compact identity between two
original ribbon presentations. The actual completed comparison supplies
its smooth extension through the original compact inclusion images. -/
theorem exists_originalNativeIdentityCompactDiffeomorph
    (hdim : k + 1 = d) (D E : LiouvilleDomain d)
    (C : Completion D) (K : Completion E)
    (μ : Form k M 1) (hμ : IsLocallyExtendibleForm μ)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative μ) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector μ (exteriorDerivative μ) x.val)))
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (eM' : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M E.domain.Point ∞)
    (hp : ∀ x, (D.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) (fun y => (eM y).val) x) = μ x)
    (hp' : ∀ x, (E.liouville.primitive (eM' x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) (fun y => (eM' y).val) x) = μ x)
    (hc : HasNativeCoordinateExtensions (k := k) D.domain.extension (fun x => (eM x).val))
    (hc' : HasNativeCoordinateExtensions (k := k) E.domain.extension (fun x => (eM' x).val)) :
    ∃ g : CompactDomainDiffeomorph D.domain E.domain,
      (∀ x, g.map (eM x).val = (eM' x).val) ∧
      (∀ x, g.inverse (eM' x).val = (eM x).val) ∧
      ∀ z ∈ D.domain.carrier,
        D.domain.extension.pullback E.domain.extension g.map E.liouville.primitive z =
          D.liouville.primitive z := by
  subst d
  let P := NativeLiouvillePresentation.of_endpoint μ D eM hp hc
  let Q := NativeLiouvillePresentation.of_endpoint μ E eM' hp' hc'
  obtain ⟨f, _, hs, hi, _⟩ := exists_strictNativeSliceComparison μ hμ hnd hout P Q C K
  obtain ⟨g, hg, hgi⟩ := C.exists_compactDiffeomorph_of_native_squares K eM eM' f hs hi
  have hmd (x : M) : MDifferentiableAt 𝓘(ℝ, Model (k + 1))
      𝓘(ℝ, Model (k + 1)) g.map (P.inclusion x) :=
    (g.smooth_map.contMDiffAt (g.open_source.mem_nhds
      (g.contains_source (eM x).property))).mdifferentiableAt (by simp)
  refine ⟨g, hg, hgi, ?_⟩
  intro z hz
  obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
  have hx' : (eM x).val = z := congrArg Subtype.val hx
  rw [← hx']
  change D.domain.extension.pullback E.domain.extension g.map E.liouville.primitive
    (P.inclusion x) = D.liouville.primitive (P.inclusion x)
  simpa only [one_smul] using NativeCompactMap.primitive_scaled_of_native_square
    D.domain.extension E.domain.extension P.inclusion Q.inclusion
    P.smooth_inclusion Q.smooth_inclusion P.tangent_bijective
    (Diffeomorph.refl (𝓡∂ (k + 1)) M ∞) g.map hmd hg
    D.liouville.primitive E.liouville.primitive μ μ hp hp' 1
    (fun y => by simp; ext vs; rfl) x

end IntrinsicLiouville

namespace CompletionIdentification
open IntrinsicLiouville

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Independently prescribed pairs representing the same native ambient,
full ribbon, primitives and witnesses admit a permitted identification on
those exact pairs. Both completed and compact maps are constructed. The
induced boundary identification and its zero shift follow from the native
boundary inclusion squares, and the full ribbon square follows at radius
zero. No ambient comparison or ribbon trajectory match is assumed. -/
theorem exists_of_same_native_pair
    (P Q : WitnessedPair n) (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (lam : Form a A 1) (hlam : IsLocallyExtendibleForm lam)
    (hAnd : ∀ x, Nondegenerate (exteriorDerivative lam) x)
    (hAout : ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector lam (exteriorDerivative lam) x.val)))
    (μ : Form k M 1) (hμ : IsLocallyExtendibleForm μ)
    (hMnd : ∀ x, Nondegenerate (exteriorDerivative μ) x)
    (hMout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector μ (exteriorDerivative μ) x.val)))
    (eA : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A P.ambientDomain.domain.Point ∞)
    (eA' : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A Q.ambientDomain.domain.Point ∞)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞)
    (eM' : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M Q.ribbonDomain.domain.Point ∞)
    (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv P.ambientDomain.domain.boundary)
    (eB' : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv Q.ambientDomain.domain.boundary)
    (hpA : ∀ x, (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eA y).val) x) = lam x)
    (hpA' : ∀ x, (Q.ambientDomain.liouville.primitive (eA' x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eA' y).val) x) = lam x)
    (hpM : ∀ x, (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = μ x)
    (hpM' : ∀ x, (Q.ribbonDomain.liouville.primitive (eM' x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM' y).val) x) = μ x)
    (hcA : HasNativeCoordinateExtensions (k := a) P.ambientDomain.domain.extension (fun x => (eA x).val))
    (hcA' : HasNativeCoordinateExtensions (k := a) Q.ambientDomain.domain.extension (fun x => (eA' x).val))
    (hcM : HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => (eM x).val))
    (hcM' : HasNativeCoordinateExtensions (k := k) Q.ribbonDomain.domain.extension (fun x => (eM' x).val))
    (hB : ∀ x, P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val)
    (hB' : ∀ x, Q.ambientDomain.domain.boundaryInclusion.map (eB' x) = (eA' x.val).val)
    (j : M → IntrinsicBoundary.Point a A)
    (hj : ∀ x, P.ribbonEmbedding.map (eM x).val = eB (j x))
    (hj' : ∀ x, Q.ribbonEmbedding.map (eM' x).val = eB' (j x))
    (b : IntrinsicBoundary.Point a A → ℝ)
    (hb : ∀ x, P.witness (eB x) = b x)
    (hb' : ∀ x, Q.witness (eB' x) = b x) :
    ∃ I : CompletionIdentification P Q,
      I.scale = 1 ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eM' x).val) ∧
      (∀ x, I.ribbonEquiv.inverse (eM' x).val = (eM x).val) ∧
      (∀ x, I.boundaryEquiv (eB x) = eB' x) ∧
      (∀ x, I.shift x = 0) ∧
      (∀ x, Q.witness (I.boundaryEquiv x) = P.witness x) ∧
      (∀ x, I.ambientEquiv (P.ambientCompletion.inclusion.map (eA x).val) =
        Q.ambientCompletion.inclusion.map (eA' x).val) ∧
      (∀ x, I.ambientEquiv.symm (Q.ambientCompletion.inclusion.map (eA' x).val) =
        P.ambientCompletion.inclusion.map (eA x).val) ∧
      (∀ x r, I.ambientEquiv (P.ambientCompletion.endMap (eB x, r)) =
        Q.ambientCompletion.endMap (eB' x, r)) := by
  obtain ⟨f, hf, hcompact, hinverse, hend⟩ :=
    exists_strictNativeComparison_with_boundary_square hdimA
      P.ambientDomain Q.ambientDomain P.ambientCompletion Q.ambientCompletion
      lam hlam hAnd hAout eA eA' hpA hpA' hcA hcA' eB eB' hB hB'
  obtain ⟨g, hg, hgi, hgp⟩ := exists_originalNativeIdentityCompactDiffeomorph hdimM
    P.ribbonDomain Q.ribbonDomain P.ribbonCompletion Q.ribbonCompletion
    μ hμ hMnd hMout eM eM' hpM hpM' hcM hcM'
  have htrajectory (z : P.ribbonDomain.domain.extension.Point)
      (hz : z ∈ P.ribbonDomain.domain.carrier) : ∃ r : ℝ,
      f (P.ambientCompletion.endMap (P.ribbonEmbedding.map z, 0)) =
        Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (g.map z), r) := by
    obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
    have hx' : (eM x).val = z := congrArg Subtype.val hx
    refine ⟨0, ?_⟩
    rw [← hx', hg, hj, hj']
    exact hend (j x) 0
  obtain ⟨I, hIf, hIg, hc⟩ := exists_of_ribbon_trajectory_square P Q f hf g 1
    (by norm_num) (by simpa only [one_smul] using hgp) htrajectory
  have hboundary (x : IntrinsicBoundary.Point a A) : I.boundaryEquiv (eB x) = eB' x := by
    obtain ⟨r0, hr⟩ := I.induced_at_infinity (eB x)
    have he := hr r0 le_rfl
    rw [hIf, hend] at he
    exact (congrArg Prod.fst (Q.ambientCompletion.endMap_injective he)).symm
  have hshift (z : P.ambientDomain.domain.boundary.Point) : I.shift z = 0 := by
    obtain ⟨x, rfl⟩ := eB.surjective z
    obtain ⟨r0, hr⟩ := I.induced_at_infinity (eB x)
    have he := hr r0 le_rfl
    rw [hIf, hend] at he
    have hs := congrArg Prod.snd (Q.ambientCompletion.endMap_injective he)
    dsimp only at hs
    change I.shift (eB x) = 0
    linarith
  refine ⟨I, hc, ?_, ?_, hboundary, hshift, ?_, ?_, ?_, ?_⟩
  · simpa only [hIg] using hg
  · simpa only [hIg] using hgi
  · intro z
    obtain ⟨x, rfl⟩ := eB.surjective z
    change Q.witness (I.boundaryEquiv (eB x)) = P.witness (eB x)
    rw [hboundary, hb, hb']
  · simpa only [hIf] using hcompact
  · simpa only [hIf] using hinverse
  · simpa only [hIf] using hend

end CompletionIdentification

namespace PairDeformation

/-- Record both original endpoint presentations as explicit permitted
steps on either side of this exact completed pair deformation. -/
def originalEndpointChain {n : ℕ} (Q : PairDeformation n)
    {P₀ P₁ : WitnessedPair n}
    (I₀ : CompletionIdentification P₀ Q.source)
    (I₁ : CompletionIdentification P₁ Q.target) : ComparisonChain P₀ P₁ :=
  ((Quiver.Path.nil.cons (ComparisonStep.identification I₀)).cons
    (ComparisonStep.deformation Q)).cons (ComparisonStep.reverse (ComparisonStep.identification I₁))

@[simp] theorem originalEndpointChain_length {n : ℕ} (Q : PairDeformation n)
    {P₀ P₁ : WitnessedPair n}
    (I₀ : CompletionIdentification P₀ Q.source)
    (I₁ : CompletionIdentification P₁ Q.target) :
    (Q.originalEndpointChain I₀ I₁).length = 3 := rfl

end PairDeformation

namespace IntrinsicLiouville

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original joint native data construct ONE actual pair deformation,
retaining all coherence and coordinate conclusions of the existing producer.
Every independently prescribed original slice presenting those same native
data is identified with that very produced slice. These identifications are
pointwise in the parameter; no joint completed comparison is asserted. -/
theorem exists_intrinsic_pairDeformation_with_original_slice_identifications
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (lam : Parameter → Form a A 1) (hlam : IsLocallyExtendibleFormFamily lam)
    (hAnd : ∀ t x, Nondegenerate (exteriorDerivative (lam t)) x)
    (hAout : ∀ t, ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (lam t) (exteriorDerivative (lam t)) x.val)))
    (μ : Parameter → Form k M 1) (hμ : IsLocallyExtendibleFormFamily μ)
    (hMnd : ∀ t x, Nondegenerate (exteriorDerivative (μ t)) x)
    (hMout : ∀ t, ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (μ t) (exteriorDerivative (μ t)) x.val)))
    (j : Parameter → M → IntrinsicBoundary.Point a A)
    (hjs : IsLocallyExtendibleMapFamily (k := k) (IntrinsicBoundary.smoothManifold a A) j)
    (hjinj : ∀ t, Function.Injective (j t))
    (hjimm : ∀ t x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x))
    (b : Parameter → IntrinsicBoundary.Point a A → ℝ)
    (hb : (IntrinsicBoundary.smoothManifold a A).IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x,
      ((b t (j t x) • IntrinsicBoundary.restrictForm (lam t) (j t x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x) = μ t x)
    (O : Parameter → WitnessedPair n)
    (eAO : ∀ t, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A (O t).ambientDomain.domain.Point ∞)
    (eMO : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M (O t).ribbonDomain.domain.Point ∞)
    (eBO : ∀ t, (IntrinsicBoundary.smoothManifold a A).SmoothEquiv (O t).ambientDomain.domain.boundary)
    (hpAO : ∀ t x, ((O t).ambientDomain.liouville.primitive (eAO t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAO t y).val) x) = lam t x)
    (hpMO : ∀ t x, ((O t).ribbonDomain.liouville.primitive (eMO t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eMO t y).val) x) = μ t x)
    (hcAO : ∀ t, HasNativeCoordinateExtensions (k := a) (O t).ambientDomain.domain.extension
      (fun x => (eAO t x).val))
    (hcMO : ∀ t, HasNativeCoordinateExtensions (k := k) (O t).ribbonDomain.domain.extension
      (fun x => (eMO t x).val))
    (hBO : ∀ t x, (O t).ambientDomain.domain.boundaryInclusion.map (eBO t x) = (eAO t x.val).val)
    (hjO : ∀ t x, (O t).ribbonEmbedding.map (eMO t x).val = eBO t (j t x))
    (hbO : ∀ t x, (O t).witness (eBO t x) = b t x) :
    ∃ Q : PairDeformation n,
    ∃ (eAs : ∀ t, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A
        (Q.pair t).ambientDomain.domain.Point ∞)
      (eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
        (Q.pair t).ribbonDomain.domain.Point ∞)
      (eBs : ∀ t, (IntrinsicBoundary.smoothManifold a A).SmoothEquiv
        (Q.pair t).ambientDomain.domain.boundary),
    ∃ (RA : ℝ → Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A A ∞)
      (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞),
      IsJointlySmoothDiffeomorphFamily (𝓡∂ (a + 1)) RA ∧
      IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM ∧
      (∀ t x, (Q.ambientPresentation t).extensionEquiv
        ((eAs parameterZero (RA t.val x)).val) = (eAs t x).val) ∧
      (∀ t x, (Q.ribbonPresentation t).extensionEquiv
        ((eMs parameterZero (RM t.val x)).val) = (eMs t x).val) ∧
      (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x) ∧
      (∀ t : Parameter,
      let P := Q.pair t
      (∀ x, P.ambientDomain.domain.boundaryInclusion.map ((eBs t) x) = ((eAs t) x.val).val) ∧
      (∀ x, (P.ambientDomain.liouville.primitive ((eAs t) x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => ((eAs t) y).val) x) = lam t x) ∧
      (IntrinsicBoundary.smoothManifold a A).pullback P.ambientDomain.domain.boundary (eBs t)
        (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
          IntrinsicBoundary.restrictForm (lam t) ∧
      (∀ x, P.ribbonEmbedding.map ((eMs t) x).val = (eBs t) (j t x)) ∧
      (∀ x, P.witness ((eBs t) x) = b t x) ∧
      (∀ x, (P.ribbonDomain.liouville.primitive ((eMs t) x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => ((eMs t) y).val) x) = μ t x) ∧
      P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = (eBs t) '' range (j t) ∧
      P.embeddedCore = (fun x => (eBs t) (j t x)) '' {x | ∀ s : ℝ, 0 ≤ s →
        P.ribbonCompletion.ambient.completeFlow.flow s
          (P.ribbonCompletion.inclusion.map ((eMs t) x).val) ∈
            range (fun y => P.ribbonCompletion.inclusion.map ((eMs t) y).val)} ∧
      HasNativeCoordinateExtensions (k := a) P.ambientDomain.domain.extension (fun x => ((eAs t) x).val) ∧
      HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => ((eMs t) x).val) ∧
      ∃ I : CompletionIdentification (O t) P,
        I.scale = 1 ∧
        (∀ x, I.ribbonEquiv.map (eMO t x).val = (eMs t x).val) ∧
        (∀ x, I.ribbonEquiv.inverse (eMs t x).val = (eMO t x).val) ∧
        (∀ x, I.boundaryEquiv (eBO t x) = eBs t x) ∧
        (∀ x, I.shift x = 0) ∧
        (∀ x, P.witness (I.boundaryEquiv x) = (O t).witness x) ∧
        (∀ x, I.ambientEquiv ((O t).ambientCompletion.inclusion.map (eAO t x).val) =
          P.ambientCompletion.inclusion.map (eAs t x).val) ∧
        (∀ x, I.ambientEquiv.symm (P.ambientCompletion.inclusion.map (eAs t x).val) =
          (O t).ambientCompletion.inclusion.map (eAO t x).val) ∧
        (∀ x r, I.ambientEquiv ((O t).ambientCompletion.endMap (eBO t x, r)) =
          P.ambientCompletion.endMap (eBs t x, r))) ∧
      ∃ (I₀ : CompletionIdentification (O parameterZero) Q.source)
        (I₁ : CompletionIdentification (O parameterOne) Q.target)
        (path : ComparisonChain (O parameterZero) (O parameterOne)),
        path = Q.originalEndpointChain I₀ I₁ ∧ path.length = 3 ∧
        I₀.scale = 1 ∧ I₁.scale = 1 ∧
        (∀ x, Q.source.witness (I₀.boundaryEquiv x) = (O parameterZero).witness x) ∧
        (∀ x, Q.target.witness (I₁.boundaryEquiv x) = (O parameterOne).witness x) := by
  obtain ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hAs, hMs, hBs, hQ⟩ :=
    exists_intrinsic_pairDeformation_with_native_coherence_and_coordinates hdimA hdimM
      lam hlam hAnd hAout μ hμ hMnd hMout j hjs hjinj hjimm b hb hpositive hribbon
  have hslice (t : Parameter) :=
    let ⟨hB, hA, _, hjQ, hbQ, hM, _, _, hcA, hcM⟩ := hQ t
    CompletionIdentification.exists_of_same_native_pair
      (O t) (Q.pair t) hdimA hdimM
      (lam t) (hlam.slice t) (hAnd t) (hAout t) (μ t) (hμ.slice t) (hMnd t) (hMout t)
      (eAO t) (eAs t) (eMO t) (eMs t) (eBO t) (eBs t)
      (hpAO t) hA (hpMO t) hM (hcAO t) hcA (hcMO t) hcM
      (hBO t) hB (j t) (hjO t) hjQ (b t) (hbO t) hbQ
  refine ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hAs, hMs, hBs, ?_, ?_⟩
  · intro t
    obtain ⟨hB, hA, hBA, hjQ, hbQ, hM, himage, hcore, hcA, hcM⟩ := hQ t
    refine ⟨hB, hA, hBA, hjQ, hbQ, hM, himage, hcore, hcA, hcM, ?_⟩
    exact hslice t
  · obtain ⟨I₀, hI₀⟩ := hslice parameterZero
    obtain ⟨I₁, hI₁⟩ := hslice parameterOne
    exact ⟨I₀, I₁, Q.originalEndpointChain I₀ I₁, rfl, rfl,
      hI₀.1, hI₁.1, hI₀.2.2.2.2.2.1, hI₁.2.2.2.2.2.1⟩

end IntrinsicLiouville
end FsFltz.Geometry
