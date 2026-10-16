import FsFltz.Geometry.ImmersionNeighborhood
import FsFltz.Geometry.Identification
import FsFltz.Geometry.Deformation
import FsFltz.Geometry.BoundaryIntrinsicEquiv

/-!
# Neighborhood presentations of prescribed compact maps

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189, and
`sec:lean`, lines 805–814. A smooth compact diffeomorphism may be represented
on open neighborhoods of its compact pieces. The construction retains its
prescribed forward map; no diffeomorphism of the original global extension
manifolds is required. The inverse on the neighborhood is constructed by
the inverse function theorem.

This is a foundation for represented compact maps. The producer from an
arbitrary native compact diffeomorphism is a separate correspondence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
namespace SmoothManifold

/-- A same-dimensional smooth map which embeds its compact carrier has a
smooth diffeomorphism presentation on neighborhoods of that carrier and its
image. Its forward map is exactly the prescribed extension on the whole
chosen source neighborhood. -/
theorem exists_smoothEquiv_neighborhood {d : ℕ}
    (M N : SmoothManifold d) (K : Set M.Point) (hK : IsCompact K)
    (f : M.Point → N.Point) (W : Set M.Point)
    (hW : IsOpen W) (hKW : K ⊆ W)
    (hf : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ f W)
    (hinj : InjOn f K)
    (himm : ∀ x ∈ K, Function.Injective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x)) :
    ∃ (U : TopologicalSpace.Opens M.Point) (_hKU : K ⊆ U)
      (V : TopologicalSpace.Opens N.Point)
      (e : (M.restrict U).SmoothEquiv (N.restrict V)),
      (U : Set M.Point) ⊆ W ∧ ∀ x, (e x).val = f x.val := by
  obtain ⟨U, hKU, j, hUW, hj⟩ :=
    M.exists_smooth_embedding_neighborhood N K hK f W hW hKW hf hinj himm
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ j.map := by
    intro x
    apply isLocalDiffeomorphAt_of_bijective_mfderiv_manifold isOpen_univ
      j.map.contMDiff.contMDiffOn (mem_univ x)
    exact ⟨j.immersion x, LinearMap.injective_iff_surjective.mp (j.immersion x)⟩
  let V : TopologicalSpace.Opens N.Point := hlocal.image
  let g : U → V := fun x => ⟨j.map x, mem_range_self x⟩
  have hgbij : Function.Bijective g := by
    constructor
    · intro x y hxy
      exact j.embedding.injective (congrArg Subtype.val hxy)
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  let e₀ := Equiv.ofBijective g hgbij
  have hes : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ e₀ :=
    (ContMDiff.subtypeVal_comp_iff V e₀).mp j.map.contMDiff
  have heis : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ e₀.symm := by
    intro y
    obtain ⟨q, hxq, hq⟩ := hlocal (e₀.symm y)
    have hqy : q (e₀.symm y) = y.val :=
      (hq hxq).symm.trans (congrArg Subtype.val (e₀.apply_symm_apply y))
    have hyq : y.val ∈ q.target := hqy ▸ q.map_source hxq
    have hqs := q.contMDiffOn_invFun.contMDiffAt (q.open_target.mem_nhds hyq)
    apply (hqs.comp y contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt.eventually_mem
      (q.open_target.mem_nhds hyq)] with z hz
    apply j.embedding.injective
    have hqz : j.map (q.invFun z.val) = z.val :=
      (hq (q.map_target hz)).trans (q.right_inv hz)
    exact (congrArg Subtype.val (e₀.apply_symm_apply z)).trans hqz.symm
  let e : (M.restrict U).SmoothEquiv (N.restrict V) :=
    { e₀ with contMDiff_toFun := hes, contMDiff_invFun := heis }
  exact ⟨U, hKU, V, e, hUW, hj⟩

end SmoothManifold

namespace CompactDomain

/-- A carrier-preserving ambient diffeomorphism induces the actual smooth
boundary diffeomorphism, using the constructed frontier atlases. No boundary
map is supplied as additional input. This also includes dimension zero. -/
theorem exists_boundaryEquiv_of_extensionEquiv {d : ℕ} (D E : CompactDomain d)
    (e : D.extension.SmoothEquiv E.extension)
    (he : e '' D.carrier = E.carrier) :
    ∃ b : D.boundary.SmoothEquiv E.boundary,
      ∀ x, e (D.boundaryInclusion.map x) = E.boundaryInclusion.map (b x) := by
  have hfront : e '' frontier D.carrier = frontier E.carrier := by
    change e.toHomeomorph '' frontier D.carrier = frontier E.carrier
    rw [e.toHomeomorph.image_frontier]
    exact congrArg frontier he
  have hset : frontier D.carrier = e ⁻¹' frontier E.carrier := by
    ext x
    rw [← hfront]
    exact e.injective.mem_set_image.symm
  let q := e.toHomeomorph.sets hset
  cases d with
  | zero =>
    let qe : D.zeroIntrinsicBoundary.SmoothEquiv E.zeroIntrinsicBoundary :=
      { q.toEquiv with
        contMDiff_toFun := contMDiff_of_discreteTopology
        contMDiff_invFun := contMDiff_of_discreteTopology }
    let b := (D.zeroBoundaryDiffeomorph.trans qe).trans E.zeroBoundaryDiffeomorph.symm
    refine ⟨b, ?_⟩
    intro x
    have hs := congrArg Subtype.val
      (E.zeroBoundaryDiffeomorph.apply_symm_apply (qe (D.zeroBoundaryDiffeomorph x)))
    exact hs.symm
  | succ k =>
    have hqs : ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ q := by
      apply E.contMDiff_frontier_iff_val.mpr
      exact e.contMDiff.comp D.contMDiff_frontier_val
    have hqis : ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ q.symm := by
      apply D.contMDiff_frontier_iff_val.mpr
      exact e.symm.contMDiff.comp E.contMDiff_frontier_val
    let qe : D.intrinsicBoundary.SmoothEquiv E.intrinsicBoundary :=
      { q.toEquiv with contMDiff_toFun := hqs, contMDiff_invFun := hqis }
    let b := (D.boundaryDiffeomorph.trans qe).trans E.boundaryDiffeomorph.symm
    refine ⟨b, ?_⟩
    intro x
    have hs := congrArg Subtype.val
      (E.boundaryDiffeomorph.apply_symm_apply (qe (D.boundaryDiffeomorph x)))
    exact hs.symm

end CompactDomain

namespace CompactDomainDiffeomorph

/-- Local extension data of a prescribed compact diffeomorphism produce
actual presentation equivalences after restricting only the extension
neighborhoods. The forward map is retained on the whole neighborhood and
the original inverse is retained on the compact target carrier. -/
theorem exists_restrictedPresentationEquiv {d : ℕ} {D E : CompactDomain d}
    (h : CompactDomainDiffeomorph D E) :
    ∃ (U : TopologicalSpace.Opens D.extension.Point) (hDU : D.carrier ⊆ U)
      (V : TopologicalSpace.Opens E.extension.Point) (hEV : E.carrier ⊆ V)
      (p : DomainPresentationEquiv (D.restrict U hDU) (E.restrict V hEV)),
      (∀ x, (p.extensionEquiv x).val = h.map x.val) ∧
      (∀ y : V, y.val ∈ E.carrier → (p.extensionEquiv.symm y).val = h.inverse y.val) := by
  have hinj : InjOn h.map D.carrier := by
    intro x hx y hy hxy
    exact (h.left_inverse x hx).symm.trans
      ((congrArg h.inverse hxy).trans (h.left_inverse y hy))
  obtain ⟨U, hDU, V, e, _, he⟩ :=
    D.extension.exists_smoothEquiv_neighborhood E.extension D.carrier D.compact
      h.map h.sourceNeighbourhood h.open_source h.contains_source h.smooth_map hinj h.immersion
  have hEV : E.carrier ⊆ V := by
    intro y hy
    let x : U := ⟨h.inverse y, hDU (h.maps_target hy)⟩
    have hs : (e x).val = y := (he x).trans (h.right_inverse y hy)
    exact hs ▸ (e x).property
  have hcarrier : e '' (D.restrict U hDU).carrier = (E.restrict V hEV).carrier := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (e x).val ∈ E.carrier
      rw [he]
      exact h.maps_source hx
    · intro hy
      let x : U := ⟨h.inverse y.val, hDU (h.maps_target hy)⟩
      exact ⟨x, h.maps_target hy, Subtype.ext ((he x).trans (h.right_inverse y.val hy))⟩
  obtain ⟨b, hb⟩ := (D.restrict U hDU).exists_boundaryEquiv_of_extensionEquiv
    (E.restrict V hEV) e hcarrier
  let p : DomainPresentationEquiv (D.restrict U hDU) (E.restrict V hEV) :=
    { extensionEquiv := e, carrier := hcarrier, boundaryEquiv := b, boundary_square := hb }
  refine ⟨U, hDU, V, hEV, p, he, ?_⟩
  intro y hy
  have hs : e ⟨h.inverse y.val, hDU (h.maps_target hy)⟩ = y :=
    Subtype.ext ((he _).trans (h.right_inverse y.val hy))
  exact congrArg Subtype.val ((e.symm_apply_apply _).symm.trans (congrArg e.symm hs)) |>.symm

end CompactDomainDiffeomorph
end FsFltz.Geometry
