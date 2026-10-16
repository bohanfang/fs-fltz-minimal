import FsFltz.Geometry.IntrinsicNativeIdentificationFamily
import FsFltz.Geometry.IntrinsicCompletionCorrespondence
import FsFltz.Geometry.IntrinsicNativeEndpointPresentation
import FsFltz.Geometry.IntrinsicLiouvilleBoundaryPresentation
import FsFltz.Geometry.IntrinsicLiouvilleFamilyExtension
import FsFltz.Geometry.CompletionIntervalMapFamily

/-!
# Joint compact comparison germs from the native family construction

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 766–836. The real ambient presentation maps produced by
the native primitive-family construction preserve the original compact
carrier. Restricting their images to the reference collar localization
gives actual target-valued joint extensions, including native boundary
points and parameter endpoints. An independently specified reference
completion is retained through a fixed strict native comparison.

Agreement here is on the whole compact carrier. The completion-map gluing
theorem requires agreement throughout an open neighborhood: the compact
extension gives this on the interior, whereas the seam requires a separate
two-sided collar producer. No general moving-completion correspondence or
geometric target is asserted by these compact extensions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.LocalizedCompletionFamily

variable {d : ℕ} [NeZero d] {D : CompactDomain d} {L : Parameter → LiouvilleStructure D}

/-- A real ambient carrier-preserving map restricts to a genuinely
target-valued partial family on the actual reference localized extension.
The open domain contains every real parameter times the compact carrier.
Only image containment is imposed away from the carrier. -/
private theorem exists_partialMap_on_reference_localization
    (F : LocalizedCompletionFamily D L)
    (h : ℝ → DomainPresentationEquiv D D)
    (hs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv p.2)) :
    ∃ W : TopologicalSpace.Opens
        (ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point),
      (univ : Set ℝ) ×ˢ (F.collars parameterZero).localizedDomain.domain.carrier ⊆ (W : Set _) ∧
      ∃ g : W → (F.collars parameterZero).localizedDomain.domain.extension.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ g ∧
        ∀ p : W, (F.collars parameterZero).originalInclusion.map (g p) =
          (h p.val.1).extensionEquiv ((F.collars parameterZero).originalInclusion.map p.val.2) := by
  classical
  let C := F.collars parameterZero
  let a : ℝ × C.localizedDomain.domain.extension.Point → D.extension.Point :=
    fun p => (h p.1).extensionEquiv (C.originalInclusion.map p.2)
  have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ a :=
    hs.comp (contMDiff_fst.prodMk (C.originalInclusion.map.contMDiff.comp contMDiff_snd))
  have hi : IsOpenEmbedding C.originalInclusion.map :=
    (⟨D, L parameterZero⟩ : LiouvilleDomain d).symplecticNeighborhood.isOpen.isOpenEmbedding_subtypeVal.comp
      C.neighborhood.isOpen.isOpenEmbedding_subtypeVal
  let W : TopologicalSpace.Opens (ℝ × C.localizedDomain.domain.extension.Point) :=
    ⟨a ⁻¹' range C.originalInclusion.map, hi.isOpen_range.preimage ha.continuous⟩
  let g : W → C.localizedDomain.domain.extension.Point := fun p => p.property.choose
  have hgval (p : W) : C.originalInclusion.map (g p) = a p.val := p.property.choose_spec
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff C.neighborhood g).mp
    apply (ContMDiff.subtypeVal_comp_iff
      (⟨D, L parameterZero⟩ : LiouvilleDomain d).symplecticNeighborhood (fun p => (g p).val)).mp
    exact (ha.comp contMDiff_subtype_val).congr hgval
  refine ⟨W, ?_, g, hg, hgval⟩
  intro p hp
  have hc : (h p.1).extensionEquiv (C.originalInclusion.map p.2) ∈ D.carrier :=
    ((h p.1).mem_carrier_iff _).mpr hp.2
  refine ⟨(C.originalPointDiffeomorph.symm ⟨a p, hc⟩).val, ?_⟩
  exact congrArg Subtype.val (C.originalPointDiffeomorph.apply_symm_apply ⟨a p, hc⟩)

/-- The actual real forward and inverse ambient presentations produce
joint target-valued extensions on the reference completed manifold. Both
extensions contain the full compact carrier at every real parameter. -/
theorem exists_compactMapFamily_extensions (F : LocalizedCompletionFamily D L) :
    ∃ (W Wi : TopologicalSpace.Opens
        (ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point))
      (g : W → (F.collars parameterZero).localizedDomain.domain.extension.Point)
      (gi : Wi → (F.collars parameterZero).localizedDomain.domain.extension.Point),
      (univ : Set ℝ) ×ˢ (F.collars parameterZero).localizedDomain.domain.carrier ⊆ (W : Set _) ∧
      (univ : Set ℝ) ×ˢ (F.collars parameterZero).localizedDomain.domain.carrier ⊆ (Wi : Set _) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ g ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ gi ∧
      (∀ p : W, (F.collars parameterZero).originalInclusion.map (g p) =
        (F.originalPresentation p.val.1).extensionEquiv.symm
          ((F.collars parameterZero).originalInclusion.map p.val.2)) ∧
      (∀ p : Wi, (F.collars parameterZero).originalInclusion.map (gi p) =
        (F.originalPresentation p.val.1).extensionEquiv
          ((F.collars parameterZero).originalInclusion.map p.val.2)) := by
  obtain ⟨W, hW, g, hg, heq⟩ := F.exists_partialMap_on_reference_localization
    (fun s => (F.originalPresentation s).symm) F.smooth_originalPresentation_symm
  obtain ⟨Wi, hWi, gi, hgi, heqi⟩ := F.exists_partialMap_on_reference_localization
    F.originalPresentation F.smooth_originalPresentation
  exact ⟨W, Wi, g, gi, hW, hWi, hg, hgi, heq, heqi⟩

/-- The inverse ambient extension is the compact comparison through the
actual constructed moving completion presentation, on every original
compact point. This equation fixes which interval map the germs extend. -/
theorem compactMapFamily_extension_square
    (F : LocalizedCompletionFamily D L)
    (W : TopologicalSpace.Opens
      (ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point))
    (g : W → (F.collars parameterZero).localizedDomain.domain.extension.Point)
    (heq : ∀ p : W, (F.collars parameterZero).originalInclusion.map (g p) =
      (F.originalPresentation p.val.1).extensionEquiv.symm
        ((F.collars parameterZero).originalInclusion.map p.val.2))
    (t : Parameter) (x : D.Point)
    (hx : (t.val, (F.collars parameterZero).originalPointDiffeomorph.symm x |>.val) ∈ W) :
    g ⟨(t.val, (F.collars parameterZero).originalPointDiffeomorph.symm x |>.val), hx⟩ =
      (F.completionPresentation t).equiv.symm
        ((F.collars t).cylindricalCompletion.inclusion.map
          ((F.collars t).originalPointDiffeomorph.symm x).val) := by
  rw [F.completionPresentation_eq]
  apply (F.collars parameterZero).originalInclusion.embedding.injective
  rw [heq]
  have hx₀ := congrArg Subtype.val
    ((F.collars parameterZero).originalPointDiffeomorph.apply_symm_apply x)
  have hxt := congrArg Subtype.val ((F.collars t).originalPointDiffeomorph.apply_symm_apply x)
  change ((F.collars parameterZero).originalPointDiffeomorph.symm x).val.val = x.val at hx₀
  change ((F.collars t).originalPointDiffeomorph.symm x).val.val = x.val at hxt
  change (F.originalPresentation t.val).extensionEquiv.symm
    ((F.collars parameterZero).originalPointDiffeomorph.symm x).val.val =
      ((F.compactPresentation t).extensionEquiv.symm
        ((F.collars t).originalPointDiffeomorph.symm x).val).val.val
  rw [hx₀]
  apply (F.originalPresentation t.val).extensionEquiv.injective
  change (F.originalPresentation t.val).extensionEquiv
    ((F.originalPresentation t.val).extensionEquiv.symm x.val) = _
  rw [(F.originalPresentation t.val).extensionEquiv.apply_symm_apply]
  have hp := F.original_projection t
    ((F.compactPresentation t).extensionEquiv.symm
      ((F.collars t).originalPointDiffeomorph.symm x).val)
  rw [(F.compactPresentation t).extensionEquiv.apply_symm_apply] at hp
  exact hxt.symm.trans hp

/-- The forward ambient extension retains the inverse native compact map
on the reference localized completion. -/
theorem compactMapFamily_inverse_extension_square
    (F : LocalizedCompletionFamily D L)
    {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.Point ∞)
    (W : TopologicalSpace.Opens (ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point))
    (g : W → (F.collars parameterZero).localizedDomain.domain.extension.Point)
    (heq : ∀ p : W, (F.collars parameterZero).originalInclusion.map (g p) =
      (F.originalPresentation p.val.1).extensionEquiv
        ((F.collars parameterZero).originalInclusion.map p.val.2))
    (t : ℝ) (x : M)
    (hx : (t, ((e.trans (F.collars parameterZero).originalPointDiffeomorph.symm) x).val) ∈ W) :
    g ⟨(t, ((e.trans (F.collars parameterZero).originalPointDiffeomorph.symm) x).val), hx⟩ =
      ((e.trans (F.collars parameterZero).originalPointDiffeomorph.symm)
        ((F.transportedNativeDiffeomorph (𝓡∂ (k + 1)) e t).symm x)).val := by
  apply (F.collars parameterZero).originalInclusion.embedding.injective
  rw [heq]
  have hc (y : M) := congrArg Subtype.val
    ((F.collars parameterZero).originalPointDiffeomorph.apply_symm_apply (e y))
  change (F.originalPresentation t).extensionEquiv
    ((F.collars parameterZero).originalPointDiffeomorph.symm (e x)).val.val =
      ((F.collars parameterZero).originalPointDiffeomorph.symm
        (e ((F.transportedNativeDiffeomorph (𝓡∂ (k + 1)) e t).symm x))).val.val
  change ∀ y : M,
    ((F.collars parameterZero).originalPointDiffeomorph.symm (e y)).val.val = (e y).val at hc
  rw [hc, hc]
  exact (F.transportedNativeDiffeomorph_symm_val (𝓡∂ (k + 1)) e t x).symm

end FsFltz.Geometry.LocalizedCompletionFamily

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original joint primitive data construct target-valued compact
comparison extensions on an independently prescribed reference completion.
The supplied reference presentation and completion are retained; the fixed
strict comparison is constructed by native inward-flow uniqueness. Neither
joint compact-map germs nor a completed family comparison is an input.

The forward equation uses the constructed moving completion presentation
itself. The inverse extension retains the actual native inverse throughout
the whole compact carrier. Boundary agreement off that carrier remains the
separate two-sided collar obligation. -/
theorem exists_nativeFamily_compactMapFamily_extensions
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val)))
    (P : NativeLiouvillePresentation (α parameterZero)) (C : Completion P.domain) :
    ∃ (D : CompactDomain (k + 1))
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
      (L : Parameter → LiouvilleStructure D)
      (F : LocalizedCompletionFamily D L)
      (q : C.ambient.manifold.SmoothEquiv (F.collars parameterZero).localizedDomain.domain.extension)
      (W : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point))
      (g : W → (F.collars parameterZero).localizedDomain.domain.extension.Point)
      (Wi : TopologicalSpace.Opens (ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point))
      (gi : Wi → C.ambient.manifold.Point),
      D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      (∀ t x, ((L t).primitive (e x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (fun y => (e y).val) x) = α t x) ∧
      C.ambient.manifold.pullback (F.collars parameterZero).cylindricalCompletion.ambient.manifold
        q (F.collars parameterZero).cylindricalCompletion.ambient.primitive = C.ambient.primitive ∧
      (∀ x, q (C.inclusion.map (P.inclusion x)) =
        ((e.trans (F.collars parameterZero).originalPointDiffeomorph.symm) x).val) ∧
      parameterInterval ×ˢ (C.inclusion.map '' P.domain.domain.carrier) ⊆ (W : Set _) ∧
      parameterInterval ×ˢ (F.collars parameterZero).localizedDomain.domain.carrier ⊆ (Wi : Set _) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) 𝓘(ℝ, Model (k + 1)) ∞ gi ∧
      (∀ t x (hx : (t.val, C.inclusion.map (P.inclusion x)) ∈ W),
        g ⟨(t.val, C.inclusion.map (P.inclusion x)), hx⟩ =
          (F.completionPresentation t).equiv.symm
            ((F.collars t).cylindricalCompletion.inclusion.map
              ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val)) ∧
      (∀ (t : Parameter) x (hx : (t.val, ((e.trans (F.collars parameterZero).originalPointDiffeomorph.symm) x).val) ∈ Wi),
        gi ⟨(t.val, ((e.trans (F.collars parameterZero).originalPointDiffeomorph.symm) x).val), hx⟩ =
          C.inclusion.map (P.inclusion
            ((F.transportedNativeDiffeomorph (𝓡∂ (k + 1)) e t.val).symm x))) ∧
      HasNativeCoordinateExtensions (k := k) D.extension (fun x => (e x).val) := by
  obtain ⟨D, i, e, L, he, hi, hemb, hbij, hrange, hfrontier,
    hL, _, hpull, _, _, _, hF, hcoord⟩ :=
    exists_liouvilleFamily_with_native_presentation_and_coordinates α hα hnd hout
  let F := Classical.choice hF
  let e₀ := e.trans (F.collars parameterZero).originalPointDiffeomorph.symm
  have hp₀ := native_primitive_localizedDomain (⟨D, L parameterZero⟩ : LiouvilleDomain (k + 1))
    (F.collars parameterZero) e (α parameterZero) (fun x => by
      rw [he, show (fun y => (e y).val) = i from funext he]
      exact congrFun (hpull parameterZero) x)
  have hi₀ (x : M) : (F.collars parameterZero).originalInclusion.map (e₀ x).val = i x := by
    exact (congrArg Subtype.val ((F.collars parameterZero).originalPointDiffeomorph.apply_symm_apply (e x))).trans (he x)
  have hc₀ := hcoord.of_smooth_square D.extension
    (F.collars parameterZero).localizedDomain.domain.extension i (fun x => (e₀ x).val)
    (F.collars parameterZero).originalInclusion.map
    (F.collars parameterZero).originalInclusion.map.contMDiff hi₀
  let Q := NativeLiouvillePresentation.of_endpoint (α parameterZero)
    (F.collars parameterZero).localizedDomain e₀ hp₀ hc₀
  obtain ⟨c, δ, hδ, _, hembc, hzero, hode, _, _⟩ :=
    exists_uniform_collar_of_localDefiningFunction_outward (α parameterZero)
      (hα.slice parameterZero) (hnd parameterZero) (hout parameterZero)
  obtain ⟨q, _, hqprim, hqsquare, _, _, _, _⟩ :=
    P.exists_strictCompletionComparison_of_inwardCollar Q C
      (F.collars parameterZero).cylindricalCompletion c hδ hembc hzero hode
  obtain ⟨W₀, Wi, g₀, gi₀, hW₀, hWi, hg₀, hgi₀, hgval, hgival⟩ :=
    F.exists_compactMapFamily_extensions
  let a : ℝ × C.ambient.manifold.Point →
      ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point :=
    fun p => (p.1, q p.2)
  have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ a :=
    contMDiff_fst.prodMk (q.contMDiff.comp contMDiff_snd)
  let W : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
    ⟨a ⁻¹' W₀, W₀.isOpen.preimage ha.continuous⟩
  let b : W → W₀ := fun p => ⟨a p.val, p.property⟩
  have hb : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ b :=
    (ContMDiff.subtypeVal_comp_iff W₀ b).mp (ha.comp contMDiff_subtype_val)
  have hq (x : M) : q (C.inclusion.map (P.inclusion x)) = (e₀ x).val := hqsquare x
  refine ⟨D, e, L, F, q, W, g₀ ∘ b, Wi, q.symm ∘ gi₀,
    hL, ?_, hqprim, hq, ?_, ?_, hg₀.comp hb, q.symm.contMDiff.comp hgi₀, ?_, ?_, ?_⟩
  · intro t x
    rw [he, show (fun y => (e y).val) = i from funext he]
    exact congrFun (hpull t) x
  · rintro ⟨s, z⟩ ⟨hs, x, hx, rfl⟩
    rw [← P.carrier_range] at hx
    obtain ⟨y, rfl⟩ := hx
    change (s, q (C.inclusion.map (P.inclusion y))) ∈ W₀
    rw [hq]
    exact hW₀ ⟨mem_univ _, (e₀ y).property⟩
  · exact fun p hp => hWi ⟨mem_univ _, hp.2⟩
  · intro t x hx
    have hx₀ : (t.val, (e₀ x).val) ∈ W₀ := by
      have hh := hx
      change (t.val, q (C.inclusion.map (P.inclusion x))) ∈ W₀ at hh
      rwa [hq] at hh
    have hbarg : b ⟨(t.val, C.inclusion.map (P.inclusion x)), hx⟩ =
        ⟨(t.val, (e₀ x).val), hx₀⟩ := Subtype.ext (Prod.ext rfl (hq x))
    change g₀ (b ⟨(t.val, C.inclusion.map (P.inclusion x)), hx⟩) = _
    rw [hbarg]
    exact F.compactMapFamily_extension_square W₀ g₀ hgval t (e x) hx₀
  · intro t x hx
    have hiq := F.compactMapFamily_inverse_extension_square e Wi gi₀ hgival t.val x hx
    change q.symm (gi₀ _) = _
    rw [hiq, ← hq]
    exact q.symm_apply_apply _
  · simpa only [he] using hcoord

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.Completion

variable {d r : ℕ} {D : LiouvilleDomain d}

/-- A joint extension retaining every compact point gives the full open
neighborhood agreement required by completion-map gluing at an interior
point. Every interval point in the resulting patch has an interior compact
representative. No boundary or exterior agreement is inferred. -/
theorem exists_interiorMapFamily_germ_of_compact_extension
    (C : Completion D) (N : SmoothManifold r)
    (f : Parameter → C.ambient.manifold.Point → N.Point)
    (W : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point))
    (hW : parameterInterval ×ˢ (C.inclusion.map '' D.domain.carrier) ⊆ (W : Set _))
    (g : W → N.Point)
    (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model r) ∞ g)
    (heq : ∀ t x (_hx : x ∈ D.domain.carrier) (hp : (t.val, C.inclusion.map x) ∈ W),
      g ⟨(t.val, C.inclusion.map x), hp⟩ = f t (C.inclusion.map x))
    (t : Parameter) (z : C.ambient.manifold.Point)
    (hz : z ∈ C.inclusion.map '' interior D.domain.carrier) :
    ∃ U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point),
      (t.val, z) ∈ U ∧ ∃ a : U → N.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model r) ∞ a ∧
        ∀ s y (hy : (s.val, y) ∈ U), a ⟨(s.val, y), hy⟩ = f s y := by
  let O : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
    ⟨(univ : Set ℝ) ×ˢ (C.inclusion.map '' interior D.domain.carrier),
      isOpen_univ.prod (C.inclusion_isLocalDiffeomorph.isLocalHomeomorph.isOpenMap
        _ isOpen_interior)⟩
  let U := W ⊓ O
  let a : U → N.Point := g ∘ TopologicalSpace.Opens.inclusion
    (show (U : Set (ℝ × C.ambient.manifold.Point)) ⊆ W from inter_subset_left)
  have hzcarrier : z ∈ C.inclusion.map '' D.domain.carrier := by
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, interior_subset hx, rfl⟩
  refine ⟨U, ⟨hW ⟨t.property, hzcarrier⟩,
    ⟨mem_univ _, hz⟩⟩, a, hg.comp (contMDiff_inclusion inter_subset_left), ?_⟩
  intro s y hy
  obtain ⟨x, hx, hxy⟩ := hy.2.2
  change C.inclusion.map x = y at hxy
  subst y
  exact heq s x (interior_subset hx) hy.1

end FsFltz.Geometry.Completion
