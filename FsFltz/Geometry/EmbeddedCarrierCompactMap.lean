import FsFltz.Geometry.CommonEmbeddingCompactMap
import FsFltz.Geometry.SmoothEmbeddingFactorization
import FsFltz.Geometry.SmoothMapFiniteExtension
import FsFltz.Geometry.BoundaryPresentationBridge

/-!
# Comparing full compact carriers in an arbitrary common ambient

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189, and
`geometric-part-fsf-proof.tex`, `eq:fiberends`, lines 1208–1237.
The actual common ambient may have positive codimension. Local projected
inverses and finite map extension retain the supplied compact carriers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Function

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold.SmoothEmbedding

/-- An actual finite-dimensional smooth embedding has a smooth local
left inverse on an ambient neighborhood of each image point. -/
theorem exists_smooth_localLeftInverse {d e : ℕ}
    {N : SmoothManifold d} {M : SmoothManifold e}
    (i : N.SmoothEmbedding M) (a : N.Point) :
    ∃ U : TopologicalSpace.Opens M.Point, i.map a ∈ U ∧
      ∃ g : U → N.Point, ContMDiff 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) ∞ g ∧
        ∀ y (hy : i.map y ∈ U), g ⟨i.map y, hy⟩ = y := by
  let c := chartAt (Model e) (i.map a)
  let J : Model d →L[ℝ] Model e := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i.map a
  obtain ⟨l, hl⟩ := J.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (i.immersion a))
  let L : Model e →L[ℝ] Model d := l.toContinuousLinearMap
  let p : M.Point → Model d := L ∘ c
  let h : N.Point → Model d := p ∘ i.map
  let V : Set N.Point := i.map ⁻¹' c.source
  have hV : IsOpen V := c.open_source.preimage i.map.contMDiff.continuous
  have haV : a ∈ V := mem_chart_source _ _
  have hcs : ContMDiffOn 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) ∞ c c.source := contMDiffOn_chart
  have hps : ContMDiffOn 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) ∞ p c.source :=
    L.contMDiff.comp_contMDiffOn hcs
  have hhs : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ h V :=
    hps.comp i.map.contMDiff.contMDiffOn (fun _ hy => hy)
  have hca := (hcs.contMDiffAt (c.open_source.mem_nhds haV)).mdifferentiableAt (by simp)
  have hia := i.map.contMDiff.mdifferentiableAt (x := a) (by simp)
  have hcder : mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) c (i.map a) =
      ContinuousLinearMap.id ℝ (Model e) := mfderiv_extChartAt_self
  have hhd : mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h a =
      ContinuousLinearMap.id ℝ (Model d) := by
    change mfderiv _ _ (L ∘ (c ∘ i.map)) a = _
    rw [mfderiv_comp a L.hasMFDerivAt.mdifferentiableAt (hca.comp a hia),
      L.hasMFDerivAt.mfderiv, mfderiv_comp a hca hia, hcder]
    ext v
    change l (J v) = v
    exact congrArg (fun A : Model d →ₗ[ℝ] Model d => A v) hl
  obtain ⟨q, haq, heq⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    hV hhs haV (by rw [hhd]; exact Function.bijective_id)
  obtain ⟨S, hS, hSq⟩ := i.embedding.isInducing.isOpen_iff.mp q.open_source
  let U : TopologicalSpace.Opens M.Point :=
    ⟨S ∩ (c.source ∩ p ⁻¹' q.target),
      hS.inter (hps.continuousOn.isOpen_inter_preimage c.open_source q.open_target)⟩
  have haU : i.map a ∈ U := by
    refine ⟨?_, haV, ?_⟩
    · have h : a ∈ i.map ⁻¹' S := by rwa [hSq]
      exact h
    · change h a ∈ q.target
      rw [heq haq]
      exact q.map_source haq
  let g : U → N.Point := fun x => q.symm (p x.val)
  have hg : ContMDiff 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) ∞ g := by
    intro x
    exact (q.contMDiffOn_invFun.contMDiffAt (q.open_target.mem_nhds x.property.2.2)).comp x
      ((hps.contMDiffAt (c.open_source.mem_nhds x.property.2.1)).comp x
        contMDiff_subtype_val.contMDiffAt)
  refine ⟨U, haU, g, hg, ?_⟩
  intro y hy
  have hyq : y ∈ q.source := by
    rw [← hSq]
    exact hy.1
  change q.symm (h y) = y
  rw [heq hyq]
  exact q.left_inv hyq

end SmoothManifold.SmoothEmbedding

namespace CompactDomain

/-- Carrier containment in an embedded submanifold supplies an actual
smooth extension of its lift near the entire retained compact carrier. -/
theorem exists_smooth_lift_of_carrierImage {d e k : ℕ}
    (D : CompactDomain d) (N : SmoothManifold k) (M : SmoothManifold e)
    (j : D.extension.SmoothEmbedding M) (i : N.SmoothEmbedding M)
    (himage : j.map '' D.carrier ⊆ range i.map) :
    ∃ U : TopologicalSpace.Opens D.extension.Point, D.carrier ⊆ U ∧
      ∃ g : U → N.Point, ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model k) ∞ g ∧
        ∀ x (hxU : x ∈ U) (_hxD : x ∈ D.carrier), i.map (g ⟨x, hxU⟩) = j.map x := by
  have hpre (x : D.Point) : ∃ y : N.Point, i.map y = j.map x.val :=
    himage ⟨x.val, x.property, rfl⟩
  choose f hf using hpre
  have hlocal : ∀ x : D.Point, ∃ U : TopologicalSpace.Opens D.extension.Point,
      x.val ∈ U ∧ ∃ g : U → N.Point,
        ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model k) ∞ g ∧
        ∀ y (hyU : y ∈ U) (hyD : y ∈ D.carrier), g ⟨y, hyU⟩ = f ⟨y, hyD⟩ := by
    intro x
    obtain ⟨S, hxS, r, hr, he⟩ := i.exists_smooth_localLeftInverse (f x)
    let U : TopologicalSpace.Opens D.extension.Point :=
      ⟨j.map ⁻¹' S, S.isOpen.preimage j.map.contMDiff.continuous⟩
    have hxU : x.val ∈ U := by
      change j.map x.val ∈ S
      rwa [← hf x]
    let q : U → S := fun y => ⟨j.map y.val, y.property⟩
    have hq : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ q :=
      (ContMDiff.subtypeVal_comp_iff S q).mp
        (j.map.contMDiff.comp _root_.contMDiff_subtype_val)
    refine ⟨U, hxU, r ∘ q, hr.comp hq, ?_⟩
    intro y hyU hyD
    have hyS : i.map (f ⟨y, hyD⟩) ∈ S := by
      rw [hf]
      exact hyU
    simpa only [Function.comp_apply, q, hf] using he (f ⟨y, hyD⟩) hyS
  obtain ⟨U, hDU, g, hg, he⟩ :=
    SmoothMapExtension.exists_smoothMapExtension_of_compact D.compact f hlocal
  refine ⟨U, hDU, g, hg, ?_⟩
  intro x hxU hxD
  rw [he x hxU hxD]
  exact hf ⟨x, hxD⟩

/-- Equality on the full native compact carrier detects all derivatives,
including at its boundary. Dimension zero is handled directly. -/
theorem mfderiv_eq_of_eqOn_carrier {d e : ℕ} (D : CompactDomain d)
    (M : SmoothManifold e) {f g : D.extension.Point → M.Point}
    (hf : ∀ x ∈ D.carrier, MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x)
    (hg : ∀ x ∈ D.carrier, MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) g x)
    (he : EqOn f g D.carrier) (x : D.extension.Point) (hx : x ∈ D.carrier) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x =
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) g x := by
  by_cases hz : d = 0
  · have hsub : Subsingleton (Model d) := by rw [hz]; infer_instance
    ext v
    have hv : v = 0 := @Subsingleton.elim _ hsub v 0
    rw [hv, map_zero, map_zero]
  · let : NeZero d := ⟨hz⟩
    let p : D.Point := ⟨x, hx⟩
    have hsurj : Function.Surjective (mfderiv (𝓡∂ d) 𝓘(ℝ, Model d)
        (Subtype.val : D.Point → D.extension.Point) p) :=
      LinearMap.injective_iff_surjective.mp (D.injective_mfderiv_subtype_val p)
    have hfi := mfderiv_comp (f := (Subtype.val : D.Point → D.extension.Point))
      (g := f) p (hf x hx) (D.contMDiff_subtype_val.mdifferentiableAt (by simp))
    have hgi := mfderiv_comp (f := (Subtype.val : D.Point → D.extension.Point))
      (g := g) p (hg x hx) (D.contMDiff_subtype_val.mdifferentiableAt (by simp))
    have heq : f ∘ (Subtype.val : D.Point → D.extension.Point) =
        g ∘ (Subtype.val : D.Point → D.extension.Point) := funext (fun y => he y.property)
    rw [heq] at hfi
    have hd := hfi.symm.trans hgi
    ext v
    obtain ⟨u, rfl⟩ := hsurj v
    exact congrArg (fun L => L u) hd

/-- Equal full embedded carriers construct a compact diffeomorphism in
any ambient dimension. The embeddings need agree only on their carriers;
the constructed map's square retains every compact point. -/
theorem exists_compactDiffeomorph_of_embeddedCarrier {d e : ℕ}
    (D E : CompactDomain d) (M : SmoothManifold e) (hD : D.carrier.Nonempty)
    (j : D.extension.SmoothEmbedding M) (k : E.extension.SmoothEmbedding M)
    (himage : j.map '' D.carrier = k.map '' E.carrier) :
    ∃ h : CompactDomainDiffeomorph D E,
      (∀ x ∈ D.carrier, k.map (h.map x) = j.map x) ∧
      (∀ y ∈ E.carrier, j.map (h.inverse y) = k.map y) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hD
  obtain ⟨y₀, hy₀, _he₀⟩ := himage ▸ (show j.map x₀ ∈ j.map '' D.carrier from ⟨x₀, hx₀, rfl⟩)
  obtain ⟨U, hDU, u, hu, hju⟩ := D.exists_smooth_lift_of_carrierImage E.extension M j k
    (by rw [himage]; exact image_subset_range _ _)
  obtain ⟨V, hEV, v, hv, hkv⟩ := E.exists_smooth_lift_of_carrierImage D.extension M k j
    (by rw [← himage]; exact image_subset_range _ _)
  let f : D.extension.Point → E.extension.Point := fun x =>
    if hx : x ∈ U then u ⟨x, hx⟩ else y₀
  let g : E.extension.Point → D.extension.Point := fun y =>
    if hy : y ∈ V then v ⟨y, hy⟩ else x₀
  have hfU (x) (hx : x ∈ U) : f x = u ⟨x, hx⟩ := dite_eq_left hx
  have hgV (y) (hy : y ∈ V) : g y = v ⟨y, hy⟩ := dite_eq_left hy
  have hfs : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ f U := by
    have h : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (fun x : U => f x.val) := by
      convert hu using 1
      funext x
      exact hfU x.val x.property
    intro x hx
    exact ((contMDiffAt_subtype_iff (f := f) (x := (⟨x, hx⟩ : U))).mp (h ⟨x, hx⟩)).contMDiffWithinAt
  have hgs : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ g V := by
    have h : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (fun y : V => g y.val) := by
      convert hv using 1
      funext y
      exact hgV y.val y.property
    intro y hy
    exact ((contMDiffAt_subtype_iff (f := g) (x := (⟨y, hy⟩ : V))).mp (h ⟨y, hy⟩)).contMDiffWithinAt
  have hsf (x) (hx : x ∈ D.carrier) : k.map (f x) = j.map x := by
    rw [hfU x (hDU hx)]
    exact hju x (hDU hx) hx
  have hsg (y) (hy : y ∈ E.carrier) : j.map (g y) = k.map y := by
    rw [hgV y (hEV hy)]
    exact hkv y (hEV hy) hy
  have hmap : MapsTo f D.carrier E.carrier := by
    intro x hx
    obtain ⟨y, hy, he⟩ := himage ▸ (show j.map x ∈ j.map '' D.carrier from ⟨x, hx, rfl⟩)
    have hfy : f x = y := k.embedding.injective ((hsf x hx).trans he.symm)
    exact hfy ▸ hy
  have hinv : MapsTo g E.carrier D.carrier := by
    intro y hy
    obtain ⟨x, hx, he⟩ := himage.symm ▸ (show k.map y ∈ k.map '' E.carrier from ⟨y, hy, rfl⟩)
    have hgx : g y = x := j.embedding.injective ((hsg y hy).trans he.symm)
    exact hgx ▸ hx
  have hfd (x) (hx : x ∈ D.carrier) :=
    (hfs.contMDiffAt (U.isOpen.mem_nhds (hDU hx))).mdifferentiableAt (by simp)
  have himm (x) (hx : x ∈ D.carrier) : Function.Injective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x) := by
    have hd := D.mfderiv_eq_of_eqOn_carrier M
      (fun z hz => (k.map.contMDiff.mdifferentiableAt (by simp)).comp z (hfd z hz))
      (fun _ _ => j.map.contMDiff.mdifferentiableAt (by simp)) hsf x hx
    rw [mfderiv_comp x (k.map.contMDiff.mdifferentiableAt (by simp)) (hfd x hx)] at hd
    intro a b hab
    apply j.immersion x
    rw [← hd]
    exact congrArg (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) k.map (f x)) hab
  refine ⟨{ map := f
            inverse := g
            sourceNeighbourhood := U
            targetNeighbourhood := V
            open_source := U.isOpen
            open_target := V.isOpen
            contains_source := hDU
            contains_target := hEV
            smooth_map := hfs
            smooth_inverse := hgs
            maps_source := hmap
            maps_target := hinv
            left_inverse := ?_
            right_inverse := ?_
            immersion := himm }, hsf, hsg⟩
  · intro x hx
    apply j.embedding.injective
    exact (hsg (f x) (hmap hx)).trans (hsf x hx)
  · intro y hy
    apply k.embedding.injective
    exact (hsf (g y) (hinv hy)).trans (hsg y hy)

end CompactDomain

namespace CompactDomainDiffeomorph

/-- The full carrier square determines the actual pullback form at every
compact point, including boundary points. No square off the carrier is assumed. -/
theorem pullback_of_embeddedCarrier {d e r : ℕ} {D E : CompactDomain d}
    (h : CompactDomainDiffeomorph D E) (M : SmoothManifold e)
    (j : D.extension.SmoothEmbedding M) (k : E.extension.SmoothEmbedding M)
    (hsquare : ∀ x ∈ D.carrier, k.map (h.map x) = j.map x)
    (α : M.Form r) (x : D.extension.Point) (hx : x ∈ D.carrier) :
    D.extension.pullback E.extension h.map (E.extension.pullback M k.map α) x =
      D.extension.pullback M j.map α x := by
  have hf (z) (hz : z ∈ D.carrier) :=
    (h.smooth_map.contMDiffAt (h.open_source.mem_nhds (h.contains_source hz))).mdifferentiableAt
      (by simp)
  have hd := D.mfderiv_eq_of_eqOn_carrier M
    (fun z hz => (k.map.contMDiff.mdifferentiableAt (by simp)).comp z (hf z hz))
    (fun _ _ => j.map.contMDiff.mdifferentiableAt (by simp)) hsquare x hx
  rw [mfderiv_comp x (k.map.contMDiff.mdifferentiableAt (by simp)) (hf x hx)] at hd
  unfold SmoothManifold.pullback
  ext v
  change α (k.map (h.map x))
    (fun i => ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) k.map (h.map x)).comp
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.map x)) (v i)) = _
  rw [hd, hsquare x hx]
  rfl

end CompactDomainDiffeomorph

end FsFltz.Geometry
