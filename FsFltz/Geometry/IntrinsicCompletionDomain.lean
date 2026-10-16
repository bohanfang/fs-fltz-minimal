import FsFltz.Geometry.IntrinsicCompletionAtlas
import FsFltz.Geometry.IntrinsicCollarDomain
import FsFltz.Geometry.LocalInverse

/-!
# The original compact domain in the intrinsic completion

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158, and `sec:lean`,
lines 783–814. Regular compact-domain presentations transport through an
open smooth embedding of equal dimension. The local inverse function
theorem transports the actual defining functions and their regularity.
This allows the finite collar domain to use the full quotient as its
extension, preserving its native carrier and boundary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomain

variable {d : ℕ} (D : CompactDomain d) (N : SmoothManifold d)
  (f : D.extension.SmoothEmbedding N) (hf : IsOpenEmbedding f.map)

include hf

/-- An open embedding takes the compact carrier's frontier to precisely
the frontier of its image. Compactness excludes new frontier points outside
the image of the extension. -/
theorem image_frontier_of_openEmbedding :
    f.map '' frontier D.carrier = frontier (f.map '' D.carrier) := by
  have hp := hf.isOpenMap.preimage_frontier_eq_frontier_preimage
    f.map.contMDiff.continuous (f.map '' D.carrier)
  rw [preimage_image_eq _ hf.injective] at hp
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ f.map ⁻¹' frontier (f.map '' D.carrier)
    exact hp.symm ▸ hy
  · intro hx
    obtain ⟨y, hy, hfy⟩ :=
      (D.compact.image f.map.contMDiff.continuous).isClosed.frontier_subset hx
    refine ⟨y, ?_, hfy⟩
    rw [← hp]
    change f.map y ∈ frontier (f.map '' D.carrier)
    rwa [hfy]

/-- The transported defining function comes from a genuine smooth local
inverse. No inverse or regularity certificate is supplied separately. -/
def definingAtImage_of_openEmbedding (y : D.extension.Point)
    (hy : y ∈ frontier D.carrier) :
    BoundaryDefiningFunction N (f.map '' D.carrier) (f.map y) := by
  let B := D.defining y hy
  have hbij : Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.map y) :=
    ⟨f.immersion y, LinearMap.injective_iff_surjective.mp (f.immersion y)⟩
  let hlocal := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    isOpen_univ f.map.contMDiff.contMDiffOn (mem_univ y) hbij
  let g := hlocal.localInverse
  have hgy : g (f.map y) = y := hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  let U : Set N.Point := g.source ∩ g ⁻¹' B.neighbourhood
  have hU : IsOpen U := g.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    g.open_source B.open_neighbourhood
  have hyU : f.map y ∈ U := by
    refine ⟨hlocal.localInverse_mem_source, ?_⟩
    change g (f.map y) ∈ B.neighbourhood
    rw [hgy]
    exact B.mem_neighbourhood
  have hp := hf.isOpenMap.preimage_frontier_eq_frontier_preimage
    f.map.contMDiff.continuous (f.map '' D.carrier)
  rw [preimage_image_eq _ hf.injective] at hp
  refine
    { neighbourhood := U
      open_neighbourhood := hU
      mem_neighbourhood := hyU
      rho := B.rho ∘ g
      smooth_rho := B.smooth_rho.comp (g.contMDiffOn_toFun.mono inter_subset_left)
        (fun _ hz => hz.2)
      sublevel := ?_
      zero_level := ?_
      regular := ?_ }
  · intro z hz
    have hfg : f.map (g z) = z := hlocal.localInverse_right_inv hz.1
    have hm : z ∈ f.map '' D.carrier ↔ g z ∈ D.carrier := by
      constructor
      · rintro ⟨w, hw, he⟩
        exact hf.injective (he.trans hfg.symm) ▸ hw
      · intro hw
        exact ⟨g z, hw, hfg⟩
    exact hm.trans (B.sublevel (g z) hz.2)
  · intro z hz
    have hfg : f.map (g z) = z := hlocal.localInverse_right_inv hz.1
    have hm : z ∈ frontier (f.map '' D.carrier) ↔ g z ∈ frontier D.carrier := by
      conv_lhs => rw [← hfg]
      exact Set.ext_iff.mp hp (g z)
    exact hm.trans (B.zero_level (g z) hz.2)
  · intro hz
    have hρ : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (B.rho ∘ g) (f.map y) :=
      (B.smooth_rho.comp (g.contMDiffOn_toFun.mono inter_subset_left)
        (fun _ hz => hz.2)).contMDiffAt (hU.mem_nhds hyU)
    have heq : (B.rho ∘ g) ∘ f.map =ᶠ[𝓝 y] B.rho := by
      filter_upwards [hlocal.localInverse_eventuallyEq_left] with z hz
      exact congrArg B.rho hz
    have hd := heq.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, ℝ))
    have hc := mfderiv_comp (f := f.map) (g := B.rho ∘ g) y
      (hρ.mdifferentiableAt (by simp)) (f.map.contMDiff.mdifferentiableAt (by simp))
    rw [hc, hz, ContinuousLinearMap.zero_comp] at hd
    exact B.regular hd.symm

/-- Extend the image-point defining construction to every point of the
image carrier's frontier, with no choice of a different boundary domain. -/
def defining_of_openEmbedding (x : N.Point)
    (hx : x ∈ frontier (f.map '' D.carrier)) :
    BoundaryDefiningFunction N (f.map '' D.carrier) x := by
  let hpre : ∃ y ∈ frontier D.carrier, f.map y = x := by
    rw [← D.image_frontier_of_openEmbedding N f hf] at hx
    exact hx
  exact hpre.choose_spec.2 ▸
    D.definingAtImage_of_openEmbedding N f hf hpre.choose hpre.choose_spec.1

/-- The actual derivative of the transported defining function on a
transported tangent vector is the original defining-function derivative. -/
theorem scalarDerivative_definingAtImage_of_openEmbedding
    (y : D.extension.Point) (hy : y ∈ frontier D.carrier) (v : D.extension.Tangent y) :
    N.scalarDerivative (D.definingAtImage_of_openEmbedding N f hf y hy).rho
      (f.map y) (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.map y v) =
        D.extension.scalarDerivative (D.defining y hy).rho y v := by
  let B := D.defining y hy
  let hlocal := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    isOpen_univ f.map.contMDiff.contMDiffOn (mem_univ y)
    (show Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.map y) from
      ⟨f.immersion y, LinearMap.injective_iff_surjective.mp (f.immersion y)⟩)
  let rho := B.rho ∘ hlocal.localInverse
  have heq : rho ∘ f.map =ᶠ[𝓝 y] B.rho := by
    filter_upwards [hlocal.localInverse_eventuallyEq_left] with z hz
    exact congrArg B.rho hz
  have hgy : hlocal.localInverse (f.map y) = y :=
    hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  have hrho : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ rho (f.map y) := by
    have hb : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ B.rho
        (hlocal.localInverse (f.map y)) := by
      rw [hgy]
      exact B.smooth_rho.contMDiffAt (B.open_neighbourhood.mem_nhds B.mem_neighbourhood)
    exact hb.comp (f.map y) hlocal.localInverse_contMDiffAt
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, ℝ))
  have hc := mfderiv_comp (f := f.map) (g := rho) y
    (hrho.mdifferentiableAt (by simp)) (f.map.contMDiff.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) rho (f.map y)
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.map y v) = _
  have hv := congrArg (fun A => A v) (hc.symm.trans hd)
  exact hv

/-- Transport an existing compact-domain presentation into an open smooth
ambient of the same dimension, retaining its literal boundary manifold. -/
def mapOpenEmbedding : CompactDomain d where
  extension := N
  carrier := f.map '' D.carrier
  compact := D.compact.image f.map.contMDiff.continuous
  defining := D.defining_of_openEmbedding N f hf
  boundary := D.boundary
  boundaryInclusion :=
    { map := ⟨f.map ∘ D.boundaryInclusion.map, f.map.contMDiff.comp D.boundaryInclusion.map.contMDiff⟩
      embedding := f.embedding.comp D.boundaryInclusion.embedding
      immersion := by
        intro x
        change Function.Injective (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
          (f.map ∘ D.boundaryInclusion.map) x)
        rw [mfderiv_comp x (f.map.contMDiff.mdifferentiableAt (by simp))
          (D.boundaryInclusion.map.contMDiff.mdifferentiableAt (by simp))]
        exact (f.immersion _).comp (D.boundaryInclusion.immersion x) }
  boundary_range := by
    change range (f.map ∘ D.boundaryInclusion.map) = frontier (f.map '' D.carrier)
    rw [range_comp, D.boundary_range, D.image_frontier_of_openEmbedding N f hf]
  zero_boundary := D.zero_boundary

omit hf in
private theorem scalarDerivative_cast_defining (s : Set N.Point) {a b : N.Point}
    (h : a = b) (B : BoundaryDefiningFunction N s a)
    (W : (x : N.Point) → N.Tangent x) :
    N.scalarDerivative (h ▸ B).rho b (W b) = N.scalarDerivative B.rho a (W a) := by
  subst b
  rfl

/-- A field carried by this same smooth open embedding remains strictly
outward for the actual transported defining functions. -/
theorem outward_mapOpenEmbedding
    (Z : (x : D.extension.Point) → D.extension.Tangent x)
    (W : (x : N.Point) → N.Tangent x)
    (htransport : ∀ y ∈ D.carrier,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.map y (Z y) = W (f.map y))
    (hout : ∀ (y : D.extension.Point) (hy : y ∈ frontier D.carrier),
      0 < D.extension.scalarDerivative (D.defining y hy).rho y (Z y)) :
    ∀ (x : N.Point) (hx : x ∈ frontier (D.mapOpenEmbedding N f hf).carrier),
      0 < N.scalarDerivative ((D.mapOpenEmbedding N f hf).defining x hx).rho x (W x) := by
  intro x hx
  change x ∈ frontier (f.map '' D.carrier) at hx
  let hpre : ∃ y ∈ frontier D.carrier, f.map y = x := by
    rw [← D.image_frontier_of_openEmbedding N f hf] at hx
    exact hx
  let y := hpre.choose
  have hy : y ∈ frontier D.carrier := hpre.choose_spec.1
  have hfy : f.map y = x := hpre.choose_spec.2
  change 0 < N.scalarDerivative
    (hfy ▸ D.definingAtImage_of_openEmbedding N f hf y hy).rho x (W x)
  rw [scalarDerivative_cast_defining]
  rw [← htransport y (D.compact.isClosed.frontier_subset hy),
    D.scalarDerivative_definingAtImage_of_openEmbedding N f hf y hy (Z y)]
  exact hout y hy

end CompactDomain

namespace IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
  (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

/-- The actual finite native collar extension is a smooth open embedded
patch of the full completion, with its original finite inclusion. -/
def finitePatchEmbedding :
    (IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero).SmoothEmbedding
      (completionManifold hδ C hemb hC hboundary hinv hzero) where
  map := ⟨finiteIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val),
    contMDiff_finiteIn hδ C hemb hC hboundary hinv hzero⟩
  embedding := (isOpenEmbedding_finiteIn _ hδ hemb.injective).isEmbedding
  immersion := fun x => (bijective_mfderiv_finiteIn hδ C hemb hC hboundary hinv hzero x).1

/-- The literal original native carrier is a compact regular domain whose
extension is the actual full completion quotient. Its boundary is the
original native boundary, included along the actual zero-time seam. -/
def compactDomain [CompactSpace M] : CompactDomain (k + 1) :=
  (IntrinsicCollarGluing.compactDomain hδ C hemb hC hboundary hinv hzero).mapOpenEmbedding
    (completionManifold hδ C hemb hC hboundary hinv hzero)
    (finitePatchEmbedding hδ C hemb hC hboundary hinv hzero)
    (isOpenEmbedding_finiteIn _ hδ hemb.injective)

/-- The compact domain contains exactly the original native points. -/
@[simp] theorem compactDomain_carrier [CompactSpace M] :
    (compactDomain hδ C hemb hC hboundary hinv hzero).carrier =
      range (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) := by
  change finiteIn _ '' range (IntrinsicCollarGluing.original _) = _
  rw [← range_comp]
  rfl

/-- The boundary inclusion is the prescribed native inclusion on every
original boundary point. -/
@[simp] theorem compactDomain_boundaryInclusion [CompactSpace M]
    (b : IntrinsicBoundary.Point k M) :
    (compactDomain hδ C hemb hC hboundary hinv hzero).boundaryInclusion.map b =
      original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) b.val := by
  change finiteIn _ ((IntrinsicCollarGluing.boundaryInclusion
    hδ C hemb hC hboundary hinv hzero).map b) = _
  rw [IntrinsicCollarGluing.boundaryInclusion_map, finiteIn_original]

/-- The same boundary inclusion is literally the zero-time cylinder slice,
so subsequent flow and end equations use this exact boundary presentation. -/
theorem compactDomain_boundaryInclusion_cylinder [CompactSpace M]
    (b : IntrinsicBoundary.Point k M) :
    (compactDomain hδ C hemb hC hboundary hinv hzero).boundaryInclusion.map b =
      cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)
        (⟨(0, b), hδ, mem_univ _⟩ : Band δ (IntrinsicBoundary.Point k M)) := by
  rw [compactDomain_boundaryInclusion]
  have he := original_collar_eq_cylinder
    (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)
    (⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ : Half δ (IntrinsicBoundary.Point k M))
  simpa only [hzero b, halfToBand] using he

end IntrinsicCompletionGluing

end FsFltz.Geometry
