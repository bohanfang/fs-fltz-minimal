import FsFltz.Geometry.IntrinsicNativeCompactDiffeomorph
import FsFltz.Geometry.NativeCompactMapCompletion
import FsFltz.Geometry.CylindricalCompletion

/-!
# Prescribed native maps on the original chosen completions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189, and
`sec:lean`, lines 803–814. Independently fixed native Liouville
presentations and a prescribed native diffeomorphism produce a compact
map on simultaneous open carrier neighborhoods. Restricting the supplied
completions retains their original completed ambients, primitives, flows
and end maps. The resulting completed equivalence therefore has the
original native compact formula and inverse formula on those same spaces.

Across-boundary map smoothness is stated through actual native coordinate
germs. No global equivalence of the extension manifolds, nonempty source,
or substituted compact map is assumed. These are foundational comparison
maps, not the existence of a geometric endpoint chain or grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.IntrinsicLiouville.NativeLiouvillePresentation

variable {k : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [IsManifold (𝓡∂ (k + 1)) ∞ N]

/-- Localize a native presentation to the actual compact interior and
constructed collar. Its carrier, native primitive, full differential and
coordinate-extension germs are retained, while the existing cylindrical
construction supplies a completion of this localized domain. -/
def localized {α : Form k M 1} (P : NativeLiouvillePresentation α) :
    NativeLiouvillePresentation α := by
  let P₀ := P.restrict P.domain.symplecticNeighborhood
    P.domain.carrier_subset_symplecticNeighborhood
  let P₁ := P₀.restrict P.domain.flowCollar.neighborhood
    P.domain.flowCollar.carrier_subset_neighborhood
  exact { P₁ with domain := P.domain.flowCollar.localizedDomain }

@[simp] theorem localized_domain {α : Form k M 1} (P : NativeLiouvillePresentation α) :
    P.localized.domain = P.domain.flowCollar.localizedDomain := rfl

@[simp] theorem localized_inclusion_val {α : Form k M 1}
    (P : NativeLiouvillePresentation α) (x : M) :
    (P.localized.inclusion x).val.val = P.inclusion x := rfl

/-- The actual collar and cylindrical-flow construction supplies a
completion of the localized native presentation, with no completion input. -/
abbrev localizedCompletion {α : Form k M 1} (P : NativeLiouvillePresentation α) :
    Completion P.localized.domain := P.domain.cylindricalCompletion

variable [CompactSpace M]

/-- A prescribed native compact map extends between arbitrary original
chosen completions of two independently fixed native presentations. Both
native compact directions, the original boundary and the original end maps
are retained through the simultaneous carrier-neighborhood restrictions. -/
theorem exists_scaledCompletionEquiv_of_nativeDiffeomorph
    {α : Form k M 1} {β : Form k N 1}
    (P : NativeLiouvillePresentation α) (Q : NativeLiouvillePresentation β)
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x)
    (C : Completion P.domain) (C' : Completion Q.domain) :
    ∃ (e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
      (b : P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary),
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        c • C.ambient.primitive ∧
      (∀ x : M, e (C.inclusion.map (P.inclusion x)) = C'.inclusion.map (Q.inclusion (h x))) ∧
      (∀ y : N, e.symm (C'.inclusion.map (Q.inclusion y)) =
        C.inclusion.map (P.inclusion (h.symm y))) ∧
      (∀ x, e (C.inclusion.map (P.domain.domain.boundaryInclusion.map x)) =
        C'.inclusion.map (Q.domain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e (C.endMap (x, r)) = C'.endMap (b x, r)) := by
  obtain ⟨W, hW, U, hU, V, hV, g, hsquare, _, hprim⟩ :=
    P.exists_restrictedNativeCompactDiffeomorph Q h hgerm c hscale
  let P₁ := (P.restrict W hW).restrict U hU
  let Q₁ := Q.restrict V hV
  let C₁ := (C.restrict W hW).restrict U hU
  let C₂ := C'.restrict V hV
  obtain ⟨e, b, hp, he, _, hend⟩ := C₁.exists_scaledEquiv_of_compactDiffeomorph C₂ g c hc hprim
  have hnative (x : M) :
      e (C.inclusion.map (P.inclusion x)) = C'.inclusion.map (Q.inclusion (h x)) := by
    have hx : P₁.inclusion x ∈ P₁.domain.domain.carrier := P₁.carrier_range ▸ mem_range_self x
    have hs := he (P₁.inclusion x) hx
    rw [hsquare] at hs
    exact hs
  refine ⟨e, b, hp, hnative, ?_, ?_, hend⟩
  · intro y
    have hs := congrArg e.symm (hnative (h.symm y))
    simpa only [e.symm_apply_apply, h.apply_symm_apply] using hs.symm
  · intro x
    have hs := hend x 0 (le_refl 0)
    change e (C.endMap (x, 0)) = C'.endMap (b x, 0) at hs
    rwa [C.endMap_zero, C'.endMap_zero] at hs

/-- Scale one gives the strict completed map of the original native
diffeomorphism, preserving the same native map, inverse, boundary and end
equations on the original chosen completions. -/
theorem exists_strictCompletionEquiv_of_nativeDiffeomorph
    {α : Form k M 1} {β : Form k N 1}
    (P : NativeLiouvillePresentation α) (Q : NativeLiouvillePresentation β)
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (hprimitive : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = α x)
    (C : Completion P.domain) (C' : Completion Q.domain) :
    ∃ (e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
      (b : P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary),
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        C.ambient.primitive ∧
      (∀ x : M, e (C.inclusion.map (P.inclusion x)) = C'.inclusion.map (Q.inclusion (h x))) ∧
      (∀ y : N, e.symm (C'.inclusion.map (Q.inclusion y)) =
        C.inclusion.map (P.inclusion (h.symm y))) ∧
      (∀ x, e (C.inclusion.map (P.domain.domain.boundaryInclusion.map x)) =
        C'.inclusion.map (Q.domain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e (C.endMap (x, r)) = C'.endMap (b x, r)) := by
  simpa only [one_smul] using P.exists_scaledCompletionEquiv_of_nativeDiffeomorph Q h hgerm
    1 (by norm_num) (by simpa only [one_smul] using hprimitive) C C'

/-- Two independently fixed native presentations construct both localized
completions and a completed map of the prescribed native diffeomorphism.
The localized native inclusions retain the original points and tensors.
There is no supplied completion or completed-map premise. -/
theorem exists_scaledConstructedCompletionEquiv_of_nativeDiffeomorph
    {α : Form k M 1} {β : Form k N 1}
    (P : NativeLiouvillePresentation α) (Q : NativeLiouvillePresentation β)
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) :
    ∃ (e : P.localizedCompletion.ambient.manifold.SmoothEquiv Q.localizedCompletion.ambient.manifold)
      (b : P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary),
      P.localizedCompletion.ambient.manifold.pullback Q.localizedCompletion.ambient.manifold
        e Q.localizedCompletion.ambient.primitive = c • P.localizedCompletion.ambient.primitive ∧
      (∀ x : M, e (P.localizedCompletion.inclusion.map (P.localized.inclusion x)) =
        Q.localizedCompletion.inclusion.map (Q.localized.inclusion (h x))) ∧
      (∀ y : N, e.symm (Q.localizedCompletion.inclusion.map (Q.localized.inclusion y)) =
        P.localizedCompletion.inclusion.map (P.localized.inclusion (h.symm y))) ∧
      (∀ x, e (P.localizedCompletion.inclusion.map (P.localized.domain.domain.boundaryInclusion.map x)) =
        Q.localizedCompletion.inclusion.map (Q.localized.domain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e (P.localizedCompletion.endMap (x, r)) =
        Q.localizedCompletion.endMap (b x, r)) := by
  exact P.localized.exists_scaledCompletionEquiv_of_nativeDiffeomorph Q.localized
    h hgerm c hc hscale P.localizedCompletion Q.localizedCompletion

/-- The constructed localized completions admit the strict extension of
the prescribed primitive-preserving native diffeomorphism, with its actual
native map, inverse, boundary and end maps retained. -/
theorem exists_strictConstructedCompletionEquiv_of_nativeDiffeomorph
    {α : Form k M 1} {β : Form k N 1}
    (P : NativeLiouvillePresentation α) (Q : NativeLiouvillePresentation β)
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (hprimitive : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = α x) :
    ∃ (e : P.localizedCompletion.ambient.manifold.SmoothEquiv Q.localizedCompletion.ambient.manifold)
      (b : P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary),
      P.localizedCompletion.ambient.manifold.pullback Q.localizedCompletion.ambient.manifold
        e Q.localizedCompletion.ambient.primitive = P.localizedCompletion.ambient.primitive ∧
      (∀ x : M, e (P.localizedCompletion.inclusion.map (P.localized.inclusion x)) =
        Q.localizedCompletion.inclusion.map (Q.localized.inclusion (h x))) ∧
      (∀ y : N, e.symm (Q.localizedCompletion.inclusion.map (Q.localized.inclusion y)) =
        P.localizedCompletion.inclusion.map (P.localized.inclusion (h.symm y))) ∧
      (∀ x, e (P.localizedCompletion.inclusion.map (P.localized.domain.domain.boundaryInclusion.map x)) =
        Q.localizedCompletion.inclusion.map (Q.localized.domain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e (P.localizedCompletion.endMap (x, r)) =
        Q.localizedCompletion.endMap (b x, r)) := by
  exact P.localized.exists_strictCompletionEquiv_of_nativeDiffeomorph Q.localized
    h hgerm hprimitive P.localizedCompletion Q.localizedCompletion

end FsFltz.Geometry.IntrinsicLiouville.NativeLiouvillePresentation
