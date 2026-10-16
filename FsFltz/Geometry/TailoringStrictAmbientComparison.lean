import FsFltz.Geometry.TailoringHittingCompletionFlow
import FsFltz.Geometry.NativeCompactMapCompletion
import FsFltz.Geometry.BoundaryContact

/-!
# Strict comparison of the actual outer collar completions

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1905,
and `geoemtric-part-fsf.tex`, `def:chain`, lines 171–200. Two collar choices
on the same compact domain with the same primitive have a constructed strict
comparison whose compact square retains every native compact point. A separate
lemma gives an all-real end formula when a boundary restriction is prescribed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- The boundary map of a compact primitive preserving map is its prescribed
boundary restriction, and its completed end law holds at every real radius. -/
theorem Completion.exists_strictEquiv_with_boundary {d : ℕ} {D E : LiouvilleDomain d}
    (C : Completion D) (C' : Completion E)
    (h : CompactDomainDiffeomorph D.domain E.domain)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.map E.liouville.primitive x =
        D.liouville.primitive x)
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (hb : ∀ x, h.map (D.domain.boundaryInclusion.map x) =
      E.domain.boundaryInclusion.map (b x)) :
    ∃ e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold,
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive = C.ambient.primitive ∧
      (∀ x ∈ D.domain.carrier, e (C.inclusion.map x) = C'.inclusion.map (h.map x)) ∧
      ∀ x r, e (C.endMap (x, r)) = C'.endMap (b x, r) := by
  obtain ⟨e, b', he, hc, hb', hend⟩ := C.exists_strictEquiv_of_compactDiffeomorph C' h hp
  have heq (x) : b' x = b x :=
    E.domain.boundaryInclusion.embedding.injective ((hb' x).symm.trans (hb x))
  refine ⟨e, he, hc, ?_⟩
  intro x r
  have hz := hend x 0 le_rfl
  rw [heq] at hz
  simpa only [add_zero] using C.map_endMap_of_eq C' e he x (b x) 0 0
    (by simpa only [add_zero] using hz) r

namespace LiouvilleDomain.FlowCollar

/-- The retained original ribbon and its collar localization are related by
an actual compact map with scale exactly one. -/
theorem exists_originalCompactComparison {d : ℕ} {F : LiouvilleDomain d}
    (B : F.FlowCollar) (hF : F.domain.carrier.Nonempty) :
    ∃ h : CompactDomainDiffeomorph F.domain B.localizedDomain.domain,
      (∀ x ∈ h.sourceNeighbourhood, B.originalInclusion.map (h.map x) = x) ∧
      ∀ x ∈ F.domain.carrier,
        F.domain.extension.pullback B.localizedDomain.domain.extension h.map
          B.localizedDomain.liouville.primitive x = F.liouville.primitive x := by
  let e : F.domain.extension.SmoothEmbedding F.domain.extension :=
    { map := ⟨id, contMDiff_id⟩
      embedding := Topology.IsEmbedding.id
      immersion := by
        intro x
        change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
          (id : F.domain.extension.Point → F.domain.extension.Point) x)
        rw [mfderiv_id]
        exact Function.injective_id }
  have hemap : (e.map : F.domain.extension.Point → F.domain.extension.Point) = id := rfl
  obtain ⟨h, hsquare, _hinverse⟩ := F.domain.exists_compactDiffeomorph_of_commonEmbedding
    B.localizedDomain.domain F.domain.extension hF e B.originalInclusion
    (by rw [hemap, image_id]; exact B.image_originalInclusion_carrier.symm)
  refine ⟨h, hsquare, ?_⟩
  intro x hx
  rw [B.localized_primitive_pullback]
  have hp := h.pullback_of_commonEmbedding F.domain.extension e B.originalInclusion
    hsquare F.liouville.primitive x hx
  rw [hemap, F.domain.extension.pullback_id] at hp
  exact hp

/-- The two collar presentations carry the same whole compact domain and
the same native primitive, with their native projection square. -/
theorem exists_compactComparison_of_primitive_eq {d : ℕ}
    (D : CompactDomain d) (L L' : LiouvilleStructure D)
    (C : (⟨D, L⟩ : LiouvilleDomain d).FlowCollar)
    (C' : (⟨D, L'⟩ : LiouvilleDomain d).FlowCollar)
    (hD : D.carrier.Nonempty) (hprimitive : L.primitive = L'.primitive) :
    ∃ h : CompactDomainDiffeomorph C.localizedDomain.domain C'.localizedDomain.domain,
      (∀ x ∈ h.sourceNeighbourhood,
        C'.originalInclusion.map (h.map x) = C.originalInclusion.map x) ∧
      ∀ x ∈ C.localizedDomain.domain.carrier,
        C.localizedDomain.domain.extension.pullback C'.localizedDomain.domain.extension h.map
          C'.localizedDomain.liouville.primitive x = C.localizedDomain.liouville.primitive x := by
  have hne : C.localizedDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hD
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp C.image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  obtain ⟨h, hsquare, _hinverse⟩ :=
    C.localizedDomain.domain.exists_compactDiffeomorph_of_commonEmbedding
      C'.localizedDomain.domain D.extension hne C.originalInclusion C'.originalInclusion
      (C.image_originalInclusion_carrier.trans C'.image_originalInclusion_carrier.symm)
  refine ⟨h, hsquare, ?_⟩
  intro x hx
  rw [C'.localized_primitive_pullback, C.localized_primitive_pullback, hprimitive]
  exact h.pullback_of_commonEmbedding D.extension C.originalInclusion C'.originalInclusion
    hsquare L'.primitive x hx

/-- The actual strict ambient comparison is constructed from equality of
the full native compact carrier and primitive. Its compact map retains every
native point; its induced boundary map is constructed independently. -/
theorem exists_strictComparison_of_primitive_eq {d : ℕ}
    (D : CompactDomain d) (L L' : LiouvilleStructure D)
    (C : (⟨D, L⟩ : LiouvilleDomain d).FlowCollar)
    (C' : (⟨D, L'⟩ : LiouvilleDomain d).FlowCollar)
    (X : Completion C.localizedDomain) (X' : Completion C'.localizedDomain)
    (hD : D.carrier.Nonempty) (hprimitive : L.primitive = L'.primitive) :
    ∃ (h : CompactDomainDiffeomorph C.localizedDomain.domain C'.localizedDomain.domain)
      (e : X.ambient.manifold.SmoothEquiv X'.ambient.manifold),
      X.ambient.manifold.pullback X'.ambient.manifold e X'.ambient.primitive = X.ambient.primitive ∧
      ∀ x ∈ C.localizedDomain.domain.carrier,
        C'.originalInclusion.map (h.map x) = C.originalInclusion.map x ∧
        e (X.inclusion.map x) = X'.inclusion.map (h.map x) := by
  obtain ⟨h, hsquare, hp⟩ := C.exists_compactComparison_of_primitive_eq D L L' C' hD hprimitive
  obtain ⟨e, b, he, hc, _hb, _hend⟩ := X.exists_strictEquiv_of_compactDiffeomorph X' h hp
  exact ⟨h, e, he, fun x hx => ⟨hsquare x (h.contains_source hx), hc x hx⟩⟩

end LiouvilleDomain.FlowCollar
end FsFltz.Geometry
