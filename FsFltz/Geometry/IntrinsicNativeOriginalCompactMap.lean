import FsFltz.Geometry.IntrinsicNativeCompactDiffeomorph

/-!
# Prescribed native compact maps on the original completed presentations

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199, and
`sec:lean`, lines 805–814. The native compact map is extended locally on
restricted neighborhoods, then represented on the original endpoint domains.
The originally supplied completions provide compact fallback points for the
irrelevant values outside those neighborhoods. Smoothness is required only
near the compact carriers. Every native forward and inverse value and the
full primitive scale are retained, without replacing either endpoint.

The compact-point consequence of completion coverage includes dimension zero.
The native presentation producer itself uses the positive-dimensional model;
no geometric chain, target-specific marking or full-fiber assertion is proved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold

/-- An actual completion forces a nonempty compact carrier whenever its
original extension has a point. In the end branch, the boundary base point
is already in the compact carrier. This includes dimension zero. -/
theorem Completion.carrier_nonempty_of_extension_nonempty {d : ℕ}
    {D : LiouvilleDomain d} (C : Completion D)
    (hne : Nonempty D.domain.extension.Point) : D.domain.carrier.Nonempty := by
  obtain ⟨x⟩ := hne
  have hz : C.inclusion.map x ∈ C.inclusion.map '' D.domain.carrier ∪
      C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := C.covering ▸ mem_univ _
  rcases hz with ⟨y, hy, _⟩ | ⟨⟨b, _⟩, _, _⟩
  · exact ⟨y, hy⟩
  · exact ⟨D.domain.boundaryInclusion.map b,
      D.domain.boundaryInclusion_mem_carrier b⟩

private def compactPointOfExtension {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (x : D.domain.extension.Point) : D.domain.Point :=
  ⟨(C.carrier_nonempty_of_extension_nonempty ⟨x⟩).choose,
    (C.carrier_nonempty_of_extension_nonempty ⟨x⟩).choose_spec⟩

/-- A partial smooth map may be made total with arbitrary fallback values;
its original values and smoothness persist on its actual open domain. -/
private theorem totalize_openMap {d e : ℕ} (F : SmoothManifold d)
    (N : SmoothManifold e) (U : TopologicalSpace.Opens F.Point)
    (f : U → N.Point) (S : Set U) (hS : IsOpen S)
    (hf : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f S)
    (fallback : F.Point → N.Point) :
    ∃ g : F.Point → N.Point,
      ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ g (Subtype.val '' S) ∧
      ∀ x ∈ S, g x.val = f x := by
  classical
  let g : F.Point → N.Point := fun z =>
    if hz : z ∈ Subtype.val '' S then f hz.choose else fallback z
  have heq (x : U) (hx : x ∈ S) : g x.val = f x := by
    have hz : x.val ∈ Subtype.val '' S := ⟨x, hx, rfl⟩
    change (if hz : x.val ∈ Subtype.val '' S then f hz.choose else fallback x.val) = _
    rw [dite_eq_left hz]
    exact congrArg f (Subtype.ext hz.choose_spec.2)
  refine ⟨g, ?_, heq⟩
  rintro z ⟨x, hx, rfl⟩
  have hs : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞
      (fun y : U => g y.val) x := by
    apply (hf.contMDiffAt (hS.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds hx] with y hy
    exact heq y hy
  exact ((contMDiffAt_subtype_iff (f := g) (x := x)).mp hs).contMDiffWithinAt

namespace IntrinsicLiouville

variable {k : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [IsManifold (𝓡∂ (k + 1)) ∞ N] [CompactSpace M]

namespace NativeLiouvillePresentation

/-- The prescribed native compact diffeomorphism has an actual compact-map
representation on the original endpoint domains. Supplied completions are
used only to obtain fallback carrier points; neither domain nor completion
is replaced. The full primitive equality holds on the original carrier. -/
theorem exists_originalNativeCompactDiffeomorph
    {α : Form k M 1} {β : Form k N 1}
    (P : NativeLiouvillePresentation α) (Q : NativeLiouvillePresentation β)
    (C : Completion P.domain) (C' : Completion Q.domain)
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) :
    ∃ g : CompactDomainDiffeomorph P.domain.domain Q.domain.domain,
      (∀ x, g.map (P.inclusion x) = Q.inclusion (h x)) ∧
      (∀ y, g.inverse (Q.inclusion y) = P.inclusion (h.symm y)) ∧
      ∀ x ∈ P.domain.domain.carrier,
        P.domain.domain.extension.pullback Q.domain.domain.extension g.map
          Q.domain.liouville.primitive x = c • P.domain.liouville.primitive x := by
  classical
  obtain ⟨W, hW, U, hU, V, hV, a, hsquare, hinverse, _⟩ :=
    P.exists_restrictedNativeCompactDiffeomorph Q h hgerm c hscale
  let P₀ := P.restrict W hW
  let P₁ := P₀.restrict U hU
  let Q₁ := Q.restrict V hV
  change TopologicalSpace.Opens W at U
  let fallback : P.domain.domain.extension.Point → Q.domain.domain.extension.Point :=
    fun z => Q.inclusion (h (P.carrierEquiv.symm (compactPointOfExtension C z)))
  let fallback' : Q.domain.domain.extension.Point → P.domain.domain.extension.Point :=
    fun z => P.inclusion (h.symm (Q.carrierEquiv.symm (compactPointOfExtension C' z)))
  have hforward : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (fun x : U => (a.map x).val) a.sourceNeighbourhood :=
    contMDiff_subtype_val.comp_contMDiffOn a.smooth_map
  obtain ⟨f₀, hf₀, he₀⟩ := totalize_openMap
    (P.domain.domain.extension.restrict W) Q.domain.domain.extension U
      (fun x => (a.map x).val) a.sourceNeighbourhood a.open_source hforward
      (fun z => fallback z.val)
  let S₀ : Set W := Subtype.val '' a.sourceNeighbourhood
  have hS₀ : IsOpen S₀ := U.isOpen.isOpenMap_subtype_val _ a.open_source
  obtain ⟨f, hf, he⟩ := totalize_openMap P.domain.domain.extension
    Q.domain.domain.extension W f₀ S₀ hS₀ hf₀ fallback
  let S : Set P.domain.domain.extension.Point := Subtype.val '' S₀
  have hS : IsOpen S := W.isOpen.isOpenMap_subtype_val _ hS₀
  have hinv : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (fun y : V => (a.inverse y).val.val) a.targetNeighbourhood :=
    (contMDiff_subtype_val.comp contMDiff_subtype_val).comp_contMDiffOn a.smooth_inverse
  obtain ⟨f', hf', he'⟩ := totalize_openMap Q.domain.domain.extension
    P.domain.domain.extension V (fun y => (a.inverse y).val.val)
      a.targetNeighbourhood a.open_target hinv fallback'
  let T : Set Q.domain.domain.extension.Point := Subtype.val '' a.targetNeighbourhood
  have hT : IsOpen T := V.isOpen.isOpenMap_subtype_val _ a.open_target
  have hnative (x : M) : f (P.inclusion x) = Q.inclusion (h x) := by
    have hx : P₁.inclusion x ∈ a.sourceNeighbourhood :=
      a.contains_source (P₁.carrier_range ▸ mem_range_self x)
    have hx₀ : (P₁.inclusion x).val ∈ S₀ := ⟨P₁.inclusion x, hx, rfl⟩
    have heq := (he (P₁.inclusion x).val hx₀).trans (he₀ (P₁.inclusion x) hx)
    change f (P.inclusion x) = (a.map (P₁.inclusion x)).val at heq
    exact heq.trans (congrArg Subtype.val (hsquare x))
  have hnative' (y : N) : f' (Q.inclusion y) = P.inclusion (h.symm y) := by
    have hy : Q₁.inclusion y ∈ a.targetNeighbourhood :=
      a.contains_target (Q₁.carrier_range ▸ mem_range_self y)
    have heq := he' (Q₁.inclusion y) hy
    change f' (Q.inclusion y) = (a.inverse (Q₁.inclusion y)).val.val at heq
    exact heq.trans (congrArg (fun z => z.val.val) (hinverse y))
  have hcarrierS : P.domain.domain.carrier ⊆ S := by
    intro z hz
    rw [← P.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    exact ⟨(P₁.inclusion x).val,
      ⟨P₁.inclusion x, a.contains_source (P₁.carrier_range ▸ mem_range_self x), rfl⟩, rfl⟩
  have hcarrierT : Q.domain.domain.carrier ⊆ T := by
    intro z hz
    rw [← Q.carrier_range] at hz
    obtain ⟨y, rfl⟩ := hz
    exact ⟨Q₁.inclusion y, a.contains_target (Q₁.carrier_range ▸ mem_range_self y), rfl⟩
  have hmd (x : M) : MDifferentiableAt 𝓘(ℝ, Model (k + 1))
      𝓘(ℝ, Model (k + 1)) f (P.inclusion x) :=
    (hf.contMDiffAt (hS.mem_nhds (hcarrierS (P.carrier_range ▸ mem_range_self x)))).mdifferentiableAt
      (by simp)
  let g : CompactDomainDiffeomorph P.domain.domain Q.domain.domain :=
    { map := f
      inverse := f'
      sourceNeighbourhood := S
      targetNeighbourhood := T
      open_source := hS
      open_target := hT
      contains_source := hcarrierS
      contains_target := hcarrierT
      smooth_map := hf
      smooth_inverse := hf'
      maps_source := by
        intro z hz
        rw [← P.carrier_range] at hz
        obtain ⟨x, rfl⟩ := hz
        rw [hnative]
        exact Q.carrier_range ▸ mem_range_self _
      maps_target := by
        intro z hz
        rw [← Q.carrier_range] at hz
        obtain ⟨y, rfl⟩ := hz
        rw [hnative']
        exact P.carrier_range ▸ mem_range_self _
      left_inverse := by
        intro z hz
        rw [← P.carrier_range] at hz
        obtain ⟨x, rfl⟩ := hz
        rw [hnative, hnative', h.symm_apply_apply]
      right_inverse := by
        intro z hz
        rw [← Q.carrier_range] at hz
        obtain ⟨y, rfl⟩ := hz
        rw [hnative', hnative, h.apply_symm_apply]
      immersion := by
        intro z hz
        rw [← P.carrier_range] at hz
        obtain ⟨x, rfl⟩ := hz
        exact NativeCompactMap.injective_mfderiv_of_native_square
          P.domain.domain.extension Q.domain.domain.extension P.inclusion Q.inclusion
          P.smooth_inclusion Q.smooth_inclusion P.tangent_bijective Q.tangent_bijective
          h f hmd hnative x }
  refine ⟨g, hnative, hnative', ?_⟩
  intro z hz
  rw [← P.carrier_range] at hz
  obtain ⟨x, rfl⟩ := hz
  exact NativeCompactMap.primitive_scaled_of_native_square
    P.domain.domain.extension Q.domain.domain.extension P.inclusion Q.inclusion
    P.smooth_inclusion Q.smooth_inclusion P.tangent_bijective h f hmd hnative
    P.domain.liouville.primitive Q.domain.liouville.primitive α β
    (congrFun P.primitive) (congrFun Q.primitive) c hscale x

end NativeLiouvillePresentation
end IntrinsicLiouville
end FsFltz.Geometry
