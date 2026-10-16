import FsFltz.Geometry.IntrinsicNativeCompactMapFamilyGerms
import FsFltz.Geometry.PrescribedFamilyCollarGerms
import FsFltz.Geometry.PrescribedFamilyCollarInverse
import FsFltz.Geometry.CompletionPositiveEndMapFamily
import FsFltz.Geometry.MovingCompletionRegularity

/-!
# Comparison with the original varying completions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. Original native primitive families construct
their localized completions. Each slice is compared strictly with the
independently prescribed moving completion, using the original native
inward collar rather than an assumed family of comparison maps. Transport
back through the two actual presentations retains the varying primitive.

The prescribed presentation at zero need not be an identity or strict.
The end-family conclusion concerns the actual comparison trajectories.
Original primitive data construct the family, its strict slice maps, and
jointly smooth forward and inverse reference maps with their actual varying
pulled primitive. No geometric chain or target theorem is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville
open SmoothManifold

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The actual compact presentation transports the reference native
carrier to an independently prescribed slice. Source-coordinate germs
come from the same inverse compact map, with no joint target map input. -/
def NativeLiouvillePresentation.transportEndpoint
    {η : Form k M 1} (R : NativeLiouvillePresentation η)
    (E : LiouvilleDomain (k + 1))
    (h : DomainPresentationEquiv R.domain.domain E.domain)
    (α : Form k M 1)
    (hp : ∀ x, (E.liouville.primitive (h.extensionEquiv (R.inclusion x))).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (fun y => h.extensionEquiv (R.inclusion y)) x) = α x) :
    NativeLiouvillePresentation α := by
  let e := R.carrierEquiv.trans h.nativePointDiffeomorph
  have he (x : M) : (e x).val = h.extensionEquiv (R.inclusion x) := by
    change h.extensionEquiv (R.carrierEquiv x).val = _
    rw [R.carrier_square]
  have hc := R.coordinates.of_smooth_square R.domain.domain.extension E.domain.extension
    R.inclusion (fun x => (e x).val) h.extensionEquiv.symm
    h.extensionEquiv.symm.contMDiff (fun x => by rw [he]; exact h.extensionEquiv.symm_apply_apply _)
  let P := NativeLiouvillePresentation.of_endpoint α E e
    (fun x => by rw [show (fun y => (e y).val) =
      (fun y => h.extensionEquiv (R.inclusion y)) from funext he, he]; exact hp x) hc
  exact
    { domain := E
      inclusion := fun x => (e x).val
      carrierEquiv := e
      carrier_square := fun _ => rfl
      smooth_inclusion := P.smooth_inclusion
      embedding := P.embedding
      tangent_bijective := P.tangent_bijective
      carrier_range := P.carrier_range
      primitive := P.primitive
      differential := P.differential
      coordinates := P.coordinates }

attribute [reducible] NativeLiouvillePresentation.transportEndpoint

@[simp] theorem NativeLiouvillePresentation.transportEndpoint_inclusion
    {η : Form k M 1} (R : NativeLiouvillePresentation η)
    (E : LiouvilleDomain (k + 1))
    (h : DomainPresentationEquiv R.domain.domain E.domain)
    (α : Form k M 1) (hp) (x : M) :
    (R.transportEndpoint E h α hp).inclusion x = h.extensionEquiv (R.inclusion x) := by
  change h.extensionEquiv (R.carrierEquiv x).val = _
  rw [R.carrier_square]

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The original primitive and its inward ODE collar construct the strict
map of a slice. The all-real end square uses the SAME original native
boundary point on both independently supplied completions. -/
theorem exists_strictNativeSliceComparison
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (P Q : NativeLiouvillePresentation α)
    (C : Completion P.domain) (K : Completion Q.domain) :
    ∃ q : C.ambient.manifold.SmoothEquiv K.ambient.manifold,
      C.ambient.manifold.pullback K.ambient.manifold q K.ambient.primitive = C.ambient.primitive ∧
      (∀ x, q (C.inclusion.map (P.inclusion x)) = K.inclusion.map (Q.inclusion x)) ∧
      (∀ x, q.symm (K.inclusion.map (Q.inclusion x)) = C.inclusion.map (P.inclusion x)) ∧
      (∀ b r, q (C.endMap (P.nativeBoundaryEquiv b, r)) =
        K.endMap (Q.nativeBoundaryEquiv b, r)) := by
  obtain ⟨c, δ, hδ, _, hemb, hz, hode, _, _⟩ :=
    exists_uniform_collar_of_localDefiningFunction_outward α hα hnd hout
  obtain ⟨q, _, hp, hs, hi, _, _, hf⟩ :=
    P.exists_strictCompletionComparison_of_inwardCollar Q C K c hδ hemb hz hode
  refine ⟨q, hp, hs, hi, ?_⟩
  intro b r
  rw [C.end_flow, K.end_flow, hf, P.nativeBoundaryEquiv_inclusion,
    Q.nativeBoundaryEquiv_inclusion, hs]

/-- Pullback along the actual relative comparison retains the varying
completed primitive. In particular, the supplied reference presentation
is not silently treated as a strict map. -/
theorem relativeComparison_primitive
    {d : ℕ} {D : LiouvilleDomain d} {E : LiouvilleDomain d}
    {A : LiouvilleDomain d} {B : LiouvilleDomain d}
    (C : Completion D) (K : Completion E) (N : Completion A) (N' : Completion B)
    (h : DomainPresentationEquiv D.domain E.domain)
    (p : CompletionPresentationEquiv C K h)
    (j : DomainPresentationEquiv A.domain B.domain)
    (s : CompletionPresentationEquiv N N' j)
    (q : N'.ambient.manifold.SmoothEquiv K.ambient.manifold)
    (hq : N'.ambient.manifold.pullback K.ambient.manifold q K.ambient.primitive =
      N'.ambient.primitive) :
    N.ambient.manifold.pullback C.ambient.manifold
      ((s.equiv.trans q).trans p.equiv.symm)
      (C.ambient.manifold.pullback K.ambient.manifold p.equiv K.ambient.primitive) =
    N.ambient.manifold.pullback N'.ambient.manifold s.equiv N'.ambient.primitive := by
  let a := (s.equiv.trans q).trans p.equiv.symm
  rw [← N.ambient.manifold.pullback_comp C.ambient.manifold K.ambient.manifold
    (a.contMDiff.mdifferentiable (by simp)) (p.equiv.contMDiff.mdifferentiable (by simp))]
  have he : p.equiv ∘ a = q ∘ s.equiv := by
    funext z
    exact p.equiv.apply_symm_apply _
  rw [he, N.ambient.manifold.pullback_comp N'.ambient.manifold K.ambient.manifold
    (s.equiv.contMDiff.mdifferentiable (by simp)) (q.contMDiff.mdifferentiable (by simp)), hq]

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.LocalizedCompletionFamily

variable {d : ℕ} {D : CompactDomain d} {L : Parameter → LiouvilleStructure D}

/-- The relative map uses the two supplied presentations themselves. -/
def referenceComparison (F : LocalizedCompletionFamily D L)
    {R : LiouvilleDomain d} (C : Completion R)
    (E : Parameter → LiouvilleDomain d) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (K t) (h t))
    (q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv (K t).ambient.manifold)
    (t : Parameter) :
    (F.collars parameterZero).cylindricalCompletion.ambient.manifold.SmoothEquiv C.ambient.manifold :=
  (((F.completionPresentation t).equiv).trans (q t)).trans (p t).equiv.symm

end FsFltz.Geometry.LocalizedCompletionFamily

namespace FsFltz.Geometry.LocalizedCompletionFamily
open IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {D : CompactDomain (k + 1)} {L : Parameter → LiouvilleStructure D}

/-- Construct the proof fields on the original localized endpoint. -/
private def nativePresentationEndpoint (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    (α : Parameter → Form k M 1)
    (hp : ∀ t x, ((L t).primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (fun y => (e y).val) x) = α t x)
    (hc : HasNativeCoordinateExtensions (k := k) D.extension (fun x => (e x).val))
    (t : Parameter) : NativeLiouvillePresentation (α t) := by
  let et := e.trans (F.collars t).originalPointDiffeomorph.symm
  have hcoord := hc.of_smooth_square D.extension
    (F.collars t).localizedDomain.domain.extension (fun x => (e x).val)
    (fun x => (et x).val) (F.collars t).originalInclusion.map
    (F.collars t).originalInclusion.map.contMDiff (fun x =>
      congrArg Subtype.val ((F.collars t).originalPointDiffeomorph.apply_symm_apply (e x)))
  exact NativeLiouvillePresentation.of_endpoint (α t) (F.collars t).localizedDomain et
    (native_primitive_localizedDomain (⟨D, L t⟩ : LiouvilleDomain (k + 1))
      (F.collars t) e (α t) (hp t)) hcoord

/-- The native presentation on each SAME constructed family slice.
Its data projections are explicit, so dependent completion and boundary
types do not unfold the proof-producing endpoint construction. -/
@[reducible] def nativePresentation (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    (α : Parameter → Form k M 1)
    (hp : ∀ t x, ((L t).primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (fun y => (e y).val) x) = α t x)
    (hc : HasNativeCoordinateExtensions (k := k) D.extension (fun x => (e x).val))
    (t : Parameter) : NativeLiouvillePresentation (α t) where
  domain := (F.collars t).localizedDomain
  inclusion := fun x => ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val
  carrierEquiv := e.trans (F.collars t).originalPointDiffeomorph.symm
  carrier_square := fun _ => rfl
  smooth_inclusion := (F.nativePresentationEndpoint e α hp hc t).smooth_inclusion
  embedding := (F.nativePresentationEndpoint e α hp hc t).embedding
  tangent_bijective := (F.nativePresentationEndpoint e α hp hc t).tangent_bijective
  carrier_range := (F.nativePresentationEndpoint e α hp hc t).carrier_range
  primitive := (F.nativePresentationEndpoint e α hp hc t).primitive
  differential := (F.nativePresentationEndpoint e α hp hc t).differential
  coordinates := (F.nativePresentationEndpoint e α hp hc t).coordinates

@[simp] theorem nativePresentation_inclusion (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    (α : Parameter → Form k M 1) (hp hc) (t : Parameter) (x : M) :
    (F.nativePresentation e α hp hc t).inclusion x =
      ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val := rfl

end FsFltz.Geometry.LocalizedCompletionFamily

namespace FsFltz.Geometry.LocalizedCompletionFamily
open IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {D : CompactDomain (k + 1)} {L : Parameter → LiouvilleStructure D}

/-- The original real compact presentations produce joint extensions of
both actual reference comparison maps on their entire compact carriers.
The arbitrary prescribed compact presentations cancel through their own
completion squares; neither presentation at zero is normalized. -/
theorem exists_referenceComparison_compact_extensions
    (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    {η : Form k M 1} (R : NativeLiouvillePresentation η) (C : Completion R.domain)
    (E : Parameter → LiouvilleDomain (k + 1)) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (K t) (h t))
    (q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv (K t).ambient.manifold)
    (hs : ∀ t x, q t ((F.collars t).cylindricalCompletion.inclusion.map
        ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) =
      (K t).inclusion.map ((h t).extensionEquiv (R.inclusion x))) :
    ∃ (W : TopologicalSpace.Opens
        (ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point))
      (g : W → C.ambient.manifold.Point)
      (Wi : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point))
      (gi : Wi → (F.collars parameterZero).cylindricalCompletion.ambient.manifold.Point),
      parameterInterval ×ˢ (F.collars parameterZero).localizedDomain.domain.carrier ⊆ (W : Set _) ∧
      parameterInterval ×ˢ (C.inclusion.map '' R.domain.domain.carrier) ⊆ (Wi : Set _) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) 𝓘(ℝ, Model (k + 1)) ∞ gi ∧
      (∀ t z (_hz : z ∈ (F.collars parameterZero).localizedDomain.domain.carrier)
        (htz : (t.val, z) ∈ W), g ⟨(t.val, z), htz⟩ =
          F.referenceComparison C E K h p q t z) ∧
      (∀ t x (_hx : x ∈ R.domain.domain.carrier)
        (htx : (t.val, C.inclusion.map x) ∈ Wi), gi ⟨(t.val, C.inclusion.map x), htx⟩ =
          (F.referenceComparison C E K h p q t).symm (C.inclusion.map x)) := by
  let e₀ := e.trans (F.collars parameterZero).originalPointDiffeomorph.symm
  let a₀ := F.referenceComparison C E K h p q parameterZero
  have h₀ (x : M) : a₀ (e₀ x).val = C.inclusion.map (R.inclusion x) := by
    change (p parameterZero).equiv.symm
      (q parameterZero ((F.completionPresentation parameterZero).equiv (e₀ x).val)) = _
    rw [F.completionPresentation_zero]
    have hh := hs parameterZero x
    change q parameterZero (e₀ x).val = _ at hh
    rw [hh, ← (p parameterZero).compact_square (R.inclusion x)
      (R.carrier_range ▸ mem_range_self x)]
    exact (p parameterZero).equiv.symm_apply_apply _
  have hnative (t : Parameter) (x : M) : F.referenceComparison C E K h p q t (e₀ x).val =
      C.inclusion.map (R.inclusion
        ((F.transportedNativeDiffeomorph (𝓡∂ (k + 1)) e t.val).symm x)) := by
    let u := (F.transportedNativeDiffeomorph (𝓡∂ (k + 1)) e t.val).symm x
    have hH := F.transportedNativeDiffeomorph_square (𝓡∂ (k + 1)) e t u
    have hu : F.transportedNativeDiffeomorph (𝓡∂ (k + 1)) e t.val u = x :=
      (F.transportedNativeDiffeomorph (𝓡∂ (k + 1)) e t.val).apply_symm_apply x
    rw [hu] at hH
    change (p t).equiv.symm (q t ((F.completionPresentation t).equiv (e₀ x).val)) = _
    rw [F.completionPresentation_eq]
    change (p t).equiv.symm (q t ((F.compactPresentation t).extensionEquiv (e₀ x).val)) = _
    have hc := congrArg (fun z => (p t).equiv.symm (q t z)) hH
    refine hc.trans ?_
    have hh := hs t u
    change q t ((e.trans (F.collars t).originalPointDiffeomorph.symm) u).val = _ at hh
    rw [hh, ← (p t).compact_square (R.inclusion u) (R.carrier_range ▸ mem_range_self u)]
    exact (p t).equiv.symm_apply_apply _
  have hinative (t : Parameter) (x : M) :
      (F.referenceComparison C E K h p q t).symm (C.inclusion.map (R.inclusion x)) =
      (F.completionPresentation t).equiv.symm
        ((F.collars t).cylindricalCompletion.inclusion.map
          ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) := by
    change (F.completionPresentation t).equiv.symm
      ((q t).symm ((p t).equiv (C.inclusion.map (R.inclusion x)))) = _
    rw [(p t).compact_square (R.inclusion x) (R.carrier_range ▸ mem_range_self x), ← hs t x,
      (q t).symm_apply_apply]
  obtain ⟨W₀, W₁, g₀, g₁, hW₀, hW₁, hg₀, hg₁, he₀, he₁⟩ := F.exists_compactMapFamily_extensions
  let a : ℝ × C.ambient.manifold.Point →
      ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point :=
    fun z => (z.1, a₀.symm z.2)
  have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ a :=
    contMDiff_fst.prodMk (a₀.symm.contMDiff.comp contMDiff_snd)
  let Wi : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
    ⟨a ⁻¹' W₀, W₀.isOpen.preimage ha.continuous⟩
  let b : Wi → W₀ := fun z => ⟨a z.val, z.property⟩
  have hb : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ b :=
    (ContMDiff.subtypeVal_comp_iff W₀ b).mp (ha.comp contMDiff_subtype_val)
  refine ⟨W₁, a₀ ∘ g₁, Wi, g₀ ∘ b,
    (fun z hz => hW₁ ⟨mem_univ _, hz.2⟩), ?_, a₀.contMDiff.comp hg₁, hg₀.comp hb, ?_, ?_⟩
  · rintro ⟨s, z⟩ ⟨hs, x, hx, rfl⟩
    rw [← R.carrier_range] at hx
    obtain ⟨y, rfl⟩ := hx
    change (s, a₀.symm (C.inclusion.map (R.inclusion y))) ∈ W₀
    rw [← h₀ y, a₀.symm_apply_apply]
    exact hW₀ ⟨mem_univ _, (e₀ y).property⟩
  · intro t z hz htz
    obtain ⟨x, hx⟩ := e₀.surjective ⟨z, hz⟩
    have hxv : (e₀ x).val = z := congrArg Subtype.val hx
    subst z
    change a₀ (g₁ _) = _
    rw [F.compactMapFamily_inverse_extension_square e W₁ g₁ he₁ t.val x htz, h₀]
    exact (hnative t x).symm
  · intro t x hx htx
    rw [← R.carrier_range] at hx
    obtain ⟨y, rfl⟩ := hx
    have harg : a₀.symm (C.inclusion.map (R.inclusion y)) = (e₀ y).val := by
      rw [← h₀ y, a₀.symm_apply_apply]
    have hp₀ : (t.val, (e₀ y).val) ∈ W₀ := by
      change (t.val, a₀.symm (C.inclusion.map (R.inclusion y))) ∈ W₀ at htx
      rwa [harg] at htx
    change g₀ (b _) = _
    have hbarg : b ⟨(t.val, C.inclusion.map (R.inclusion y)), htx⟩ =
        ⟨(t.val, (e₀ y).val), hp₀⟩ := Subtype.ext (Prod.ext rfl harg)
    rw [hbarg]
    exact (F.compactMapFamily_extension_square W₀ g₀ he₀ t (e y) hp₀).trans
      (hinative t y).symm

end FsFltz.Geometry.LocalizedCompletionFamily



namespace FsFltz.Geometry.Completion

variable {d : ℕ} {D : LiouvilleDomain d}

/-- A compact point outside the compact interior is represented at radius
zero of the actual end, using the original compact boundary inclusion. -/
theorem exists_endZero_of_compact_not_interior (C : Completion D)
    (x : D.domain.extension.Point) (hx : x ∈ D.domain.carrier)
    (hxi : C.inclusion.map x ∉ C.inclusion.map '' interior D.domain.carrier) :
    ∃ b, C.endMap (b, 0) = C.inclusion.map x := by
  have hfront : x ∈ frontier D.domain.carrier := by
    rw [frontier, D.domain.compact.isClosed.closure_eq]
    exact ⟨hx, fun hi => hxi ⟨x, hi, rfl⟩⟩
  rw [← D.domain.boundary_range] at hfront
  obtain ⟨b, hb⟩ := hfront
  exact ⟨b, by rw [C.endMap_zero, hb]⟩

end FsFltz.Geometry.Completion

namespace FsFltz.Geometry.IntrinsicLiouville
open SmoothManifold

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {D : CompactDomain (k + 1)} {L : Parameter → LiouvilleStructure D}

/-- Original native primitive laws construct all strict slice comparisons
on the already constructed family and the independently prescribed moving
completions. The target native presentation is produced by its actual
compact presentation; no completed comparison family is an input. -/
theorem exists_strictMovingNativeSliceComparisons
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
    (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    (hp : ∀ t x, ((L t).primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (fun y => (e y).val) x) = α t x)
    (hc : HasNativeCoordinateExtensions (k := k) D.extension (fun x => (e x).val))
    {η : Form k M 1} (R : NativeLiouvillePresentation η)
    (E : Parameter → LiouvilleDomain (k + 1)) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain.domain (E t).domain)
    (hαnative : ∀ t x, ((E t).liouville.primitive ((h t).extensionEquiv (R.inclusion x))).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (fun y => (h t).extensionEquiv (R.inclusion y)) x) = α t x) :
    ∃ q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv (K t).ambient.manifold,
      (∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.pullback
        (K t).ambient.manifold (q t) (K t).ambient.primitive =
          (F.collars t).cylindricalCompletion.ambient.primitive) ∧
      (∀ t x, q t ((F.collars t).cylindricalCompletion.inclusion.map
          ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) =
        (K t).inclusion.map ((h t).extensionEquiv (R.inclusion x))) ∧
      (∀ t x, (q t).symm ((K t).inclusion.map ((h t).extensionEquiv (R.inclusion x))) =
        (F.collars t).cylindricalCompletion.inclusion.map
          ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) ∧
      (∀ t b r, q t ((F.collars t).cylindricalCompletion.endMap
          ((F.nativePresentation e α hp hc t).nativeBoundaryEquiv b, r)) =
        (K t).endMap ((h t).boundaryEquiv (R.nativeBoundaryEquiv b), r)) := by
  let P := F.nativePresentation e α hp hc
  let Q := fun t => R.transportEndpoint (E t) (h t) (α t) (hαnative t)
  have hex (t : Parameter) := exists_strictNativeSliceComparison (α t) (hα.slice t)
    (hnd t) (hout t) (P t) (Q t) (F.collars t).cylindricalCompletion (K t)
  choose q hq hs _ _ using hex
  have hs' (t : Parameter) (x : M) : q t
      ((F.collars t).cylindricalCompletion.inclusion.map
        ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) =
      (K t).inclusion.map ((h t).extensionEquiv (R.inclusion x)) := by
    have ht := hs t x
    change q t ((F.collars t).cylindricalCompletion.inclusion.map
      ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) =
        (K t).inclusion.map ((Q t).inclusion x) at ht
    rw [show (Q t).inclusion x = (h t).extensionEquiv (R.inclusion x) from
      R.transportEndpoint_inclusion (E t) (h t) (α t) (hαnative t) x] at ht
    exact ht
  refine ⟨q, hq, hs', ?_, ?_⟩
  · intro t x
    exact (congrArg (q t).symm (hs' t x)).symm.trans ((q t).symm_apply_apply _)
  · intro t b r
    rw [(F.collars t).cylindricalCompletion.end_flow, (K t).end_flow,
      (F.collars t).cylindricalCompletion.ambient.map_flow (K t).ambient (q t) (hq t)]
    rw [(P t).nativeBoundaryEquiv_inclusion, hs']
    rw [← R.nativeBoundaryEquiv_inclusion, (h t).boundary_square]

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicLiouville.NativeLiouvillePresentation

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Native boundary transport is determined by the original inclusion
square, even when the two native primitives differ. -/
theorem nativeBoundary_eq_of_common_square
    {α β : Form k M 1} (P : NativeLiouvillePresentation α)
    (Q : NativeLiouvillePresentation β) (D : CompactDomain (k + 1))
    (j : P.domain.domain.extension.Point → D.extension.Point)
    (j' : Q.domain.domain.extension.Point → D.extension.Point)
    (b : P.domain.domain.boundary.Point → D.boundary.Point)
    (b' : Q.domain.domain.boundary.Point → D.boundary.Point)
    (hboundary : ∀ x, j (P.domain.domain.boundaryInclusion.map x) = D.boundaryInclusion.map (b x))
    (hboundary' : ∀ x, j' (Q.domain.domain.boundaryInclusion.map x) = D.boundaryInclusion.map (b' x))
    (hsquare : ∀ x, j (P.inclusion x) = j' (Q.inclusion x))
    (x : IntrinsicBoundary.Point k M) :
    b (P.nativeBoundaryEquiv x) = b' (Q.nativeBoundaryEquiv x) := by
  apply D.boundaryInclusion.embedding.injective
  rw [← hboundary, ← hboundary', P.nativeBoundaryEquiv_inclusion,
    Q.nativeBoundaryEquiv_inclusion, hsquare]

end FsFltz.Geometry.IntrinsicLiouville.NativeLiouvillePresentation

namespace FsFltz.Geometry.LocalizedCompletionFamily
open IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {D : CompactDomain (k + 1)} {L : Parameter → LiouvilleStructure D}

/-- The original native boundary map is unchanged by collar localization
and the varying primitive. No extension of the completed end square is used. -/
theorem nativePresentation_boundary (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    (α : Parameter → Form k M 1) (hp hc) (t : Parameter)
    (x : IntrinsicBoundary.Point k M) :
    (show D.boundary.Point from
      (F.nativePresentation e α hp hc t).nativeBoundaryEquiv x) =
      (show D.boundary.Point from
        (F.nativePresentation e α hp hc parameterZero).nativeBoundaryEquiv x) := by
  apply NativeLiouvillePresentation.nativeBoundary_eq_of_common_square
    (F.nativePresentation e α hp hc t) (F.nativePresentation e α hp hc parameterZero) D
    (F.collars t).originalInclusion.map (F.collars parameterZero).originalInclusion.map
    id id (fun _ => rfl) (fun _ => rfl)
  intro y
  exact (congrArg Subtype.val ((F.collars t).originalPointDiffeomorph.apply_symm_apply (e y))).trans
    (congrArg Subtype.val ((F.collars parameterZero).originalPointDiffeomorph.apply_symm_apply (e y))).symm

end FsFltz.Geometry.LocalizedCompletionFamily

namespace FsFltz.Geometry.LocalizedCompletionFamily
open IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {D : CompactDomain (k + 1)} {L : Parameter → LiouvilleStructure D}

/-- The same native compact and all-real flow squares give both joint
reference maps. The compact extensions come from the constructed family's
real original presentations; both seam collars come from the original
transported primitives. The completed end presentation is never extended
past its stated nonnegative-radius square. -/
theorem referenceComparison_smooth_of_native_squares
    (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    (α : Parameter → Form k M 1) (hp hc)
    {η : Form k M 1} (R : NativeLiouvillePresentation η) (C : Completion R.domain)
    (E : Parameter → LiouvilleDomain (k + 1)) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (K t) (h t))
    (hprimitive : C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (K t).ambient.manifold (p t).equiv (K t).ambient.primitive))
    (q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv (K t).ambient.manifold)
    (hs : ∀ t x, q t ((F.collars t).cylindricalCompletion.inclusion.map
        ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) =
      (K t).inclusion.map ((h t).extensionEquiv (R.inclusion x)))
    (he : ∀ t b r, q t ((F.collars t).cylindricalCompletion.endMap
        ((F.nativePresentation e α hp hc t).nativeBoundaryEquiv b, r)) =
      (K t).endMap ((h t).boundaryEquiv (R.nativeBoundaryEquiv b), r)) :
    ∃ B : D.boundary.SmoothEquiv R.domain.domain.boundary,
      (∀ t b r, q t ((F.collars t).cylindricalCompletion.endMap (b, r)) =
        (K t).endMap ((h t).boundaryEquiv (B b), r)) ∧
      (∀ t b r, F.referenceComparison C E K h p q t
          ((F.completionPresentation t).prescribedEndMap (b, r)) =
        (p t).prescribedEndMap (B b, r)) ∧
      (F.collars parameterZero).cylindricalCompletion.ambient.manifold.IsSmoothIntervalMapFamily
        C.ambient.manifold (fun t => F.referenceComparison C E K h p q t) ∧
      C.ambient.manifold.IsSmoothIntervalMapFamily
        (F.collars parameterZero).cylindricalCompletion.ambient.manifold
        (fun t => (F.referenceComparison C E K h p q t).symm) := by
  let P₀ := F.nativePresentation e α hp hc parameterZero
  let B : D.boundary.SmoothEquiv R.domain.domain.boundary :=
    P₀.nativeBoundaryEquiv.symm.trans R.nativeBoundaryEquiv
  have hB (b : IntrinsicBoundary.Point k M) :
      B (show D.boundary.Point from P₀.nativeBoundaryEquiv b) = R.nativeBoundaryEquiv b := by
    exact congrArg R.nativeBoundaryEquiv (P₀.nativeBoundaryEquiv.symm_apply_apply b)
  have hend (t : Parameter) (b : D.boundary.Point) (r : ℝ) :
      q t ((F.collars t).cylindricalCompletion.endMap (b, r)) =
        (K t).endMap ((h t).boundaryEquiv (B b), r) := by
    obtain ⟨x, hx⟩ := P₀.nativeBoundaryEquiv.surjective b
    have hx' : (show D.boundary.Point from
        (F.nativePresentation e α hp hc t).nativeBoundaryEquiv x) = b :=
      (F.nativePresentation_boundary e α hp hc t x).trans hx
    have hh := he t x r
    rw [show (F.nativePresentation e α hp hc t).nativeBoundaryEquiv x = b from hx'] at hh
    exact hh.trans (congrArg (fun z => (K t).endMap ((h t).boundaryEquiv z, r))
      ((hB x).symm.trans (congrArg B hx)))
  have hcollar (t : Parameter) (b : D.boundary.Point) (r : ℝ) :
      F.referenceComparison C E K h p q t
        ((F.completionPresentation t).prescribedEndMap (b, r)) =
          (p t).prescribedEndMap (B b, r) := by
    change (p t).equiv.symm (q t ((F.completionPresentation t).equiv
      ((F.completionPresentation t).equiv.symm
        ((F.collars t).cylindricalCompletion.endMap
          ((F.compactPresentation t).boundaryEquiv b, r))))) = _
    rw [(F.completionPresentation t).equiv.apply_symm_apply]
    rw [F.boundary_compactPresentation]
    exact congrArg (p t).equiv.symm (hend t b r)
  obtain ⟨W, g, Wi, gi, hW, hWi, hg, hgi, hgs, hgis⟩ :=
    F.exists_referenceComparison_compact_extensions e R C E K h p q hs
  have hW' : parameterInterval ×ˢ
      ((F.collars parameterZero).cylindricalCompletion.inclusion.map ''
        (F.collars parameterZero).localizedDomain.domain.carrier) ⊆
      (W : Set (ℝ × (F.collars parameterZero).localizedDomain.domain.extension.Point)) := by
    change parameterInterval ×ˢ (id '' (F.collars parameterZero).localizedDomain.domain.carrier) ⊆ _
    simpa only [image_id] using hW
  have hforward := (F.collars parameterZero).cylindricalCompletion.isSmoothIntervalMapFamily_of_compact_extension_prescribed_collar_square C
      (fun t => (F.collars t).localizedDomain) (fun t => (F.collars t).cylindricalCompletion)
      F.compactPresentation F.completionPresentation F.completedPrimitive_smooth
      E K h p hprimitive (fun t => F.referenceComparison C E K h p q t)
      B W hW' g hg hgs hcollar
  have hreverse (t : Parameter) (b : R.domain.domain.boundary.Point) (r : ℝ) :
      (F.referenceComparison C E K h p q t).symm ((p t).prescribedEndMap (b, r)) =
        (F.completionPresentation t).prescribedEndMap (B.symm b, r) := by
    have hh := congrArg (F.referenceComparison C E K h p q t).symm (hcollar t (B.symm b) r)
    rw [(F.referenceComparison C E K h p q t).symm_apply_apply, B.apply_symm_apply] at hh
    exact hh.symm
  have hinverse := C.isSmoothIntervalMapFamily_of_compact_extension_prescribed_collar_square
      (F.collars parameterZero).cylindricalCompletion E K h p hprimitive
      (fun t => (F.collars t).localizedDomain) (fun t => (F.collars t).cylindricalCompletion)
      F.compactPresentation F.completionPresentation F.completedPrimitive_smooth
      (fun t => (F.referenceComparison C E K h p q t).symm)
      B.symm Wi hWi gi hgi hgis hreverse
  exact ⟨B, hend, hcollar, hforward, hinverse⟩

end FsFltz.Geometry.LocalizedCompletionFamily

namespace FsFltz.Geometry.IntrinsicLiouville
open SmoothManifold

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original native primitive data construct one localized completion
family and its strict comparisons with the independently prescribed moving
completions. Both relative reference maps are jointly smooth. The compact
and all-real moving collar squares, nonnegative reference end squares, and
actual varying pulled primitive are retained for these SAME maps.

Only original native smoothness, symplecticity and outwardness and the
original transported completed primitive regularity are supplied. There is
no constructed-family, comparison-map, compact-germ or collar-germ input,
and no time-zero normalization requirement. -/
theorem exists_strictMovingNativeCompletionComparison
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
    {η : Form k M 1} (R : NativeLiouvillePresentation η) (C : Completion R.domain)
    (E : Parameter → LiouvilleDomain (k + 1)) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (K t) (h t))
    (hαnative : ∀ t x, ((E t).liouville.primitive ((h t).extensionEquiv (R.inclusion x))).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (fun y => (h t).extensionEquiv (R.inclusion y)) x) = α t x)
    (hprimitive : C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (K t).ambient.manifold (p t).equiv (K t).ambient.primitive)) :
    ∃ (D : CompactDomain (k + 1))
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
      (L : Parameter → LiouvilleStructure D) (F : LocalizedCompletionFamily D L)
      (q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv (K t).ambient.manifold)
      (B : D.boundary.SmoothEquiv R.domain.domain.boundary),
      D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      (∀ t x, ((L t).primitive (e x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (fun y => (e y).val) x) = α t x) ∧
      HasNativeCoordinateExtensions (k := k) D.extension (fun x => (e x).val) ∧
      (∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.pullback
        (K t).ambient.manifold (q t) (K t).ambient.primitive =
          (F.collars t).cylindricalCompletion.ambient.primitive) ∧
      (∀ t x, q t ((F.collars t).cylindricalCompletion.inclusion.map
          ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) =
        (K t).inclusion.map ((h t).extensionEquiv (R.inclusion x))) ∧
      (∀ t x, (q t).symm ((K t).inclusion.map ((h t).extensionEquiv (R.inclusion x))) =
        (F.collars t).cylindricalCompletion.inclusion.map
          ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) ∧
      (∀ t x, F.referenceComparison C E K h p q t
          ((F.completionPresentation t).equiv.symm
            ((F.collars t).cylindricalCompletion.inclusion.map
              ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val)) =
        C.inclusion.map (R.inclusion x)) ∧
      (∀ t x, (F.referenceComparison C E K h p q t).symm (C.inclusion.map (R.inclusion x)) =
        (F.completionPresentation t).equiv.symm
          ((F.collars t).cylindricalCompletion.inclusion.map
            ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val)) ∧
      (∀ t b r, q t ((F.collars t).cylindricalCompletion.endMap (b, r)) =
        (K t).endMap ((h t).boundaryEquiv (B b), r)) ∧
      (∀ t b r, F.referenceComparison C E K h p q t
          ((F.completionPresentation t).prescribedEndMap (b, r)) =
        (p t).prescribedEndMap (B b, r)) ∧
      (F.collars parameterZero).cylindricalCompletion.ambient.manifold.IsSmoothIntervalMapFamily
        C.ambient.manifold (fun t => F.referenceComparison C E K h p q t) ∧
      C.ambient.manifold.IsSmoothIntervalMapFamily
        (F.collars parameterZero).cylindricalCompletion.ambient.manifold
        (fun t => (F.referenceComparison C E K h p q t).symm) ∧
      (∀ t, (F.collars parameterZero).cylindricalCompletion.ambient.manifold.pullback
        C.ambient.manifold (F.referenceComparison C E K h p q t)
        (C.ambient.manifold.pullback (K t).ambient.manifold (p t).equiv (K t).ambient.primitive) =
        (F.collars parameterZero).cylindricalCompletion.ambient.manifold.pullback
          (F.collars t).cylindricalCompletion.ambient.manifold
          (F.completionPresentation t).equiv (F.collars t).cylindricalCompletion.ambient.primitive) ∧
      (∀ t b r, 0 ≤ r → F.referenceComparison C E K h p q t
          ((F.collars parameterZero).cylindricalCompletion.endMap (b, r)) = C.endMap (B b, r)) ∧
      (∀ t b r, 0 ≤ r → (F.referenceComparison C E K h p q t).symm
          (C.endMap (b, r)) =
        (F.collars parameterZero).cylindricalCompletion.endMap (B.symm b, r)) := by
  obtain ⟨D, i, e, L, he, _, _, _, _, _, hL, _, hpull, _, _, _, hF, hcoord⟩ :=
    exists_liouvilleFamily_with_native_presentation_and_coordinates α hα hnd hout
  let F := Classical.choice hF
  have hp (t : Parameter) (x : M) : ((L t).primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (fun y => (e y).val) x) = α t x := by
    rw [he, show (fun y => (e y).val) = i from funext he]
    exact congrFun (hpull t) x
  have hc : HasNativeCoordinateExtensions (k := k) D.extension (fun x => (e x).val) := by
    simpa only [he] using hcoord
  obtain ⟨q, hq, hs, hi, heq⟩ := exists_strictMovingNativeSliceComparisons α hα hnd hout
    F e hp hc R E K h hαnative
  obtain ⟨B, hend, hcollar, hforward, hinverse⟩ :=
    F.referenceComparison_smooth_of_native_squares e α hp hc R C E K h p hprimitive q hs heq
  have hcompact (t : Parameter) (x : M) : F.referenceComparison C E K h p q t
      ((F.completionPresentation t).equiv.symm
        ((F.collars t).cylindricalCompletion.inclusion.map
          ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val)) =
      C.inclusion.map (R.inclusion x) := by
    change (p t).equiv.symm (q t ((F.completionPresentation t).equiv
      ((F.completionPresentation t).equiv.symm _))) = _
    rw [(F.completionPresentation t).equiv.apply_symm_apply, hs,
      ← (p t).compact_square (R.inclusion x) (R.carrier_range ▸ mem_range_self x)]
    exact (p t).equiv.symm_apply_apply _
  have hicompact (t : Parameter) (x : M) :
      (F.referenceComparison C E K h p q t).symm (C.inclusion.map (R.inclusion x)) =
        (F.completionPresentation t).equiv.symm
          ((F.collars t).cylindricalCompletion.inclusion.map
            ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val) := by
    exact (congrArg (F.referenceComparison C E K h p q t).symm (hcompact t x)).symm.trans
      ((F.referenceComparison C E K h p q t).symm_apply_apply _)
  refine ⟨D, e, L, F, q, B, hL, hp, hc, hq, hs, hi, hcompact, hicompact,
    hend, hcollar, hforward, hinverse,
    ?_, ?_, ?_⟩
  · intro t
    exact relativeComparison_primitive C (K t) (F.collars parameterZero).cylindricalCompletion
      (F.collars t).cylindricalCompletion (h t) (p t) (F.compactPresentation t)
      (F.completionPresentation t) (q t) (hq t)
  · intro t b r hr
    have hh := hcollar t b r
    rw [(F.completionPresentation t).prescribedEndMap_nonnegative b r hr,
      (p t).prescribedEndMap_nonnegative (B b) r hr] at hh
    exact hh
  · intro t b r hr
    have hh := congrArg (F.referenceComparison C E K h p q t).symm (hcollar t (B.symm b) r)
    rw [(F.referenceComparison C E K h p q t).symm_apply_apply, B.apply_symm_apply,
      (F.completionPresentation t).prescribedEndMap_nonnegative (B.symm b) r hr,
      (p t).prescribedEndMap_nonnegative b r hr] at hh
    exact hh.symm

end FsFltz.Geometry.IntrinsicLiouville
