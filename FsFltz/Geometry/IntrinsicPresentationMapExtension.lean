import FsFltz.Geometry.IntrinsicPresentationCollarComparison
import FsFltz.Geometry.IntrinsicLiouvilleCollar
import FsFltz.Geometry.IntrinsicInterior

/-!
# Extending the original native identity across the compact boundary

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158,
`def:chain`, lines 171–189, and `sec:lean`, lines 805–813.
The native interior gives inverse-function germs. At the boundary the actual
completion collars agree with the same native inward trajectories. Compact
smooth-map patching then extends the native identity to an open neighborhood.
No source-chart extension of either original inclusion is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville.NativeLiouvillePresentation
open SmoothManifold

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

omit [T2Space M] [SecondCountableTopology M] in
private theorem exists_nativeIdentity_germ_interior {α : Form k M 1}
    (P Q : NativeLiouvillePresentation α) (x : IntrinsicInterior.Point k M) :
    ∃ (O : TopologicalSpace.Opens P.domain.domain.extension.Point),
      P.inclusion x.val ∈ O ∧ ∃ g : O → Q.domain.domain.extension.Point,
        ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
        ∀ y (hy : P.inclusion y ∈ O), g ⟨P.inclusion y, hy⟩ = Q.inclusion y := by
  let i : IntrinsicInterior.Point k M → P.domain.domain.extension.Point :=
    P.inclusion ∘ Subtype.val
  have hi : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i :=
    P.smooth_inclusion.comp IntrinsicInterior.contMDiff_val
  have hbij : Function.Bijective
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) := by
    rw [mfderiv_comp x (P.smooth_inclusion.mdifferentiableAt (by simp))
      (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))]
    exact (P.tangent_bijective x.val).comp (IntrinsicInterior.bijective_mfderiv_val x)
  obtain ⟨q, hxq, hq⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    isOpen_univ hi.contMDiffOn (mem_univ x) hbij
  let O : TopologicalSpace.Opens P.domain.domain.extension.Point := ⟨q.target, q.open_target⟩
  let j : IntrinsicInterior.Point k M → Q.domain.domain.extension.Point :=
    Q.inclusion ∘ Subtype.val
  have hj : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j :=
    Q.smooth_inclusion.comp IntrinsicInterior.contMDiff_val
  let g : O → Q.domain.domain.extension.Point := fun z => j (q.invFun z.val)
  have hg : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g :=
    hj.comp (q.contMDiffOn_invFun.comp_contMDiff contMDiff_subtype_val (fun z => z.property))
  refine ⟨O, ?_, g, hg, ?_⟩
  · change i x ∈ q.target
    rw [hq hxq]
    exact q.map_source hxq
  · intro y hy
    have hz : q.invFun (P.inclusion y) ∈ q.source := q.map_target hy
    have he : P.inclusion (q.invFun (P.inclusion y)).val = P.inclusion y :=
      (hq hz).trans (q.right_inv hy)
    exact congrArg Q.inclusion (P.embedding.injective he)

private theorem exists_nativeIdentity_germ_boundary {α : Form k M 1}
    (P Q : NativeLiouvillePresentation α) (C : Completion P.domain)
    (K : Completion Q.domain) (c : ℝ × IntrinsicBoundary.Point k M → M)
    {δ : ℝ} (hδ : 0 < δ)
    (hemb : Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => c p.val))
    (hzero : ∀ b, c (0, b) = b.val)
    (hode : ∀ b, IsMIntegralCurveOn (fun t => c (t, b))
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ))
    (x : IntrinsicBoundary.Point k M) :
    ∃ (O : TopologicalSpace.Opens P.domain.domain.extension.Point),
      P.inclusion x.val ∈ O ∧ ∃ g : O → Q.domain.domain.extension.Point,
        ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
        ∀ y (hy : P.inclusion y ∈ O), g ⟨P.inclusion y, hy⟩ = Q.inclusion y := by
  let A := range (fun p : Ico 0 δ ×ˢ univ => c p.val)
  have hA : IsOpen A := hemb.isOpen_range
  obtain ⟨T, hT, hTP⟩ := P.embedding.isEmbedding.isInducing.isOpen_iff.mp hA
  let W := C.compactCollarNeighborhood K (P.nativeBoundaryComparison Q)
  let O : TopologicalSpace.Opens P.domain.domain.extension.Point := ⟨T ∩ W, hT.inter W.isOpen⟩
  let a : O → W := fun z => ⟨z.val, z.property.2⟩
  have ha : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff W a).mp contMDiff_subtype_val
  refine ⟨O, ⟨?_, ?_⟩, C.compactCollarExtensionMap K (P.nativeBoundaryComparison Q) ∘ a,
    (C.contMDiff_compactCollarExtensionMap K (P.nativeBoundaryComparison Q)).comp ha, ?_⟩
  · change x.val ∈ P.inclusion ⁻¹' T
    rw [hTP]
    exact ⟨⟨(0, x), ⟨⟨le_rfl, hδ⟩, mem_univ _⟩⟩, hzero x⟩
  · change P.inclusion x.val ∈ C.compactCollarNeighborhood K (P.nativeBoundaryComparison Q)
    rw [← P.nativeBoundaryEquiv_inclusion x]
    exact C.boundary_mem_compactCollarNeighborhood K (P.nativeBoundaryComparison Q)
      (P.nativeBoundaryEquiv x)
  · intro y hy
    have hyA : y ∈ A := by
      rw [← hTP]
      exact hy.1
    obtain ⟨p, hp⟩ := hyA
    subst y
    exact P.compactCollarComparison_native_inward Q C K p.val.2
      (hode p.val.2) (hzero p.val.2) p.val.1 p.property.1 hy.2

/-- The original identity between two native presentations extends smoothly
near the entire compact carrier. The native collar is an actual open inward
ODE collar, and is subsequently produced from the original primitive data. -/
theorem exists_nativeIdentityExtension_of_inwardCollar {α : Form k M 1}
    (P Q : NativeLiouvillePresentation α) (C : Completion P.domain)
    (K : Completion Q.domain) (c : ℝ × IntrinsicBoundary.Point k M → M)
    {δ : ℝ} (hδ : 0 < δ)
    (hemb : Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => c p.val))
    (hzero : ∀ b, c (0, b) = b.val)
    (hode : ∀ b, IsMIntegralCurveOn (fun t => c (t, b))
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ)) :
    ∃ (U : TopologicalSpace.Opens P.domain.domain.extension.Point)
      (_hU : P.domain.domain.carrier ⊆ U) (g : U → Q.domain.domain.extension.Point),
      ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
      ∀ x (hx : P.inclusion x ∈ U), g ⟨P.inclusion x, hx⟩ = Q.inclusion x := by
  let f : P.domain.domain.carrier → Q.domain.domain.extension.Point :=
    fun z => Q.inclusion (P.carrierEquiv.symm z)
  have hf (x : M) (hx : P.inclusion x ∈ P.domain.domain.carrier) :
      f ⟨P.inclusion x, hx⟩ = Q.inclusion x := by
    have he : (⟨P.inclusion x, hx⟩ : P.domain.domain.carrier) = P.carrierEquiv x :=
      Subtype.ext (P.carrier_square x).symm
    simp only [f, he, P.carrierEquiv.symm_apply_apply]
  have hlocal : ∀ p : P.domain.domain.carrier,
      ∃ O : TopologicalSpace.Opens P.domain.domain.extension.Point, p.val ∈ O ∧
        ∃ g : O → Q.domain.domain.extension.Point,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
          ∀ y (hyO : y ∈ O) (hyA : y ∈ P.domain.domain.carrier),
            g ⟨y, hyO⟩ = f ⟨y, hyA⟩ := by
    intro p
    let x := P.carrierEquiv.symm p
    have hx : P.inclusion x = p.val := (P.carrier_square x).symm.trans
      (congrArg Subtype.val (P.carrierEquiv.apply_symm_apply p))
    have hgerm : ∃ O : TopologicalSpace.Opens P.domain.domain.extension.Point,
        P.inclusion x ∈ O ∧ ∃ g : O → Q.domain.domain.extension.Point,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g ∧
          ∀ y (hy : P.inclusion y ∈ O), g ⟨P.inclusion y, hy⟩ = Q.inclusion y := by
      by_cases hxb : (𝓡∂ (k + 1)).IsBoundaryPoint x
      · exact exists_nativeIdentity_germ_boundary P Q C K c hδ hemb hzero hode ⟨x, hxb⟩
      · exact exists_nativeIdentity_germ_interior P Q
          ⟨x, (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint x).mpr hxb⟩
    obtain ⟨O, hxO, g, hg, heq⟩ := hgerm
    refine ⟨O, hx ▸ hxO, g, hg, ?_⟩
    intro y hyO hyA
    rw [← P.carrier_range] at hyA
    obtain ⟨z, rfl⟩ := hyA
    exact (heq z hyO).trans (hf z _).symm
  obtain ⟨U, hU, g, hg, heq⟩ := SmoothMapExtension.exists_smoothMapExtension_of_compact
    P.domain.domain.compact f hlocal
  exact ⟨U, hU, g, hg, fun x hx =>
    (heq (P.inclusion x) hx (P.carrier_range ▸ mem_range_self x)).trans (hf x _)⟩

/-- The smooth extension of the same native identity has an invertible
differential on the carrier. The inverse function theorem supplies actual
open presentation restrictions, with the full compact primitive retained. -/
theorem exists_presentationComparison_of_inwardCollar {α : Form k M 1}
    (P Q : NativeLiouvillePresentation α) (C : Completion P.domain)
    (K : Completion Q.domain) (c : ℝ × IntrinsicBoundary.Point k M → M)
    {δ : ℝ} (hδ : 0 < δ)
    (hemb : Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => c p.val))
    (hzero : ∀ b, c (0, b) = b.val)
    (hode : ∀ b, IsMIntegralCurveOn (fun t => c (t, b))
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ)) :
    ∃ (U : TopologicalSpace.Opens P.domain.domain.extension.Point)
      (hU : P.domain.domain.carrier ⊆ U)
      (V : TopologicalSpace.Opens (P.domain.restrict U hU).domain.extension.Point)
      (hV : (P.domain.restrict U hU).domain.carrier ⊆ V)
      (W : TopologicalSpace.Opens Q.domain.domain.extension.Point)
      (hW : Q.domain.domain.carrier ⊆ W)
      (p : DomainPresentationEquiv
        ((P.domain.restrict U hU).restrict V hV).domain
        (Q.domain.restrict W hW).domain),
      (∀ x, p.extensionEquiv (((P.restrict U hU).restrict V hV).inclusion x) =
        (Q.restrict W hW).inclusion x) ∧
      ∀ z ∈ ((P.domain.restrict U hU).restrict V hV).domain.carrier,
        ((P.domain.restrict U hU).restrict V hV).domain.extension.pullback
          (Q.domain.restrict W hW).domain.extension p.extensionEquiv
          (Q.domain.restrict W hW).liouville.primitive z =
            ((P.domain.restrict U hU).restrict V hV).liouville.primitive z := by
  obtain ⟨U, hU, g, hg, heq⟩ :=
    P.exists_nativeIdentityExtension_of_inwardCollar Q C K c hδ hemb hzero hode
  let P₀ := P.restrict U hU
  have hsquare₀ (x : M) : g (P₀.inclusion x) = Q.inclusion x := heq x _
  have hginj : InjOn g P₀.domain.domain.carrier := by
    intro y hy z hz h
    rw [← P₀.carrier_range] at hy hz
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨w, rfl⟩ := hz
    rw [hsquare₀, hsquare₀] at h
    exact congrArg P₀.inclusion (Q.embedding.injective h)
  have hgimm : ∀ z ∈ P₀.domain.domain.carrier, Function.Injective
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g z) := by
    intro z hz
    rw [← P₀.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    exact injective_mfderiv_of_native_comp_on_presentation P₀.domain.domain.extension
      Q.domain.domain.extension P₀.inclusion P₀.smooth_inclusion
      (fun x => (P₀.tangent_bijective x).2) g hg Q.inclusion hsquare₀
      (fun x => (Q.tangent_bijective x).1) x
  obtain ⟨V, hV, W, e, _, he⟩ :=
    P₀.domain.domain.extension.exists_smoothEquiv_neighborhood Q.domain.domain.extension
      P₀.domain.domain.carrier P₀.domain.domain.compact g univ isOpen_univ
      (subset_univ _) hg.contMDiffOn hginj hgimm
  have hW : Q.domain.domain.carrier ⊆ W := by
    intro z hz
    rw [← Q.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    let y : V := ⟨P₀.inclusion x, hV (P₀.carrier_range ▸ mem_range_self x)⟩
    have hy : (e y).val = Q.inclusion x := (he y).trans (hsquare₀ x)
    exact hy ▸ (e y).property
  let P₁ := P₀.restrict V hV
  let Q₁ := Q.restrict W hW
  have hsquare (x : M) : e (P₁.inclusion x) = Q₁.inclusion x :=
    Subtype.ext ((he _).trans (hsquare₀ x))
  have hcarrier : e '' P₁.domain.domain.carrier = Q₁.domain.domain.carrier := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← P₁.carrier_range] at hy
      obtain ⟨x, rfl⟩ := hy
      rw [hsquare]
      exact Q₁.carrier_range ▸ mem_range_self x
    · intro hz
      rw [← Q₁.carrier_range] at hz
      obtain ⟨x, rfl⟩ := hz
      exact ⟨P₁.inclusion x, P₁.carrier_range ▸ mem_range_self x, hsquare x⟩
  obtain ⟨b, hb⟩ := P₁.domain.domain.exists_boundaryEquiv_of_extensionEquiv
    Q₁.domain.domain e hcarrier
  let p : DomainPresentationEquiv P₁.domain.domain Q₁.domain.domain :=
    { extensionEquiv := e, carrier := hcarrier, boundaryEquiv := b, boundary_square := hb }
  refine ⟨U, hU, V, hV, W, hW, p, hsquare, ?_⟩
  intro z hz
  change z ∈ P₁.domain.domain.carrier at hz
  rw [← P₁.carrier_range] at hz
  obtain ⟨x, rfl⟩ := hz
  exact pullback_eq_of_native_comp_on_presentation P₁.domain.domain.extension
    Q₁.domain.domain.extension P₁.inclusion P₁.smooth_inclusion
    (fun x => (P₁.tangent_bijective x).2) e e.contMDiff Q₁.inclusion hsquare
    Q₁.domain.liouville.primitive P₁.domain.liouville.primitive α
    (congrFun P₁.primitive) (congrFun Q₁.primitive) x

end FsFltz.Geometry.IntrinsicLiouville.NativeLiouvillePresentation
