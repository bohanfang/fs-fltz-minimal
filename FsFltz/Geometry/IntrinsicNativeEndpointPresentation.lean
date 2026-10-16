import FsFltz.Geometry.IntrinsicNativeMapCompletion

/-!
# Native presentations on already fixed compact endpoints

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 783–814. Coordinate germs are transported through the
actual smooth inclusions of carrier neighborhoods. An existing compact
native diffeomorphism and its primitive square then supply a native
Liouville presentation on that very domain. No new domain or completion
is selected by this adapter.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- Coordinate extensions pull back along an actual smooth ambient map
whose native square is literal. In particular this applies to every
carrier-neighborhood restriction used in the family construction. -/
theorem HasNativeCoordinateExtensions.of_smooth_square {d e : ℕ}
    (N : SmoothManifold d) (P : SmoothManifold e)
    (i : M → N.Point) (j : M → P.Point)
    (hi : HasNativeCoordinateExtensions (k := k) N i)
    (f : P.Point → N.Point) (hf : ContMDiff 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) ∞ f)
    (hsquare : ∀ x, f (j x) = i x) :
    HasNativeCoordinateExtensions (k := k) P j := by
  intro x
  obtain ⟨a, O, Q, ha, hO, hx, hQ, hag⟩ := hi x
  refine ⟨a, f ⁻¹' O, Q ∘ f, ha, hO.preimage hf.continuous,
    (show f (j x) ∈ O by rw [hsquare]; exact hx),
    hQ.comp hf.contMDiffOn (fun _ hz => hz), ?_⟩
  intro y hy
  change f (j y) ∈ O at hy
  rw [hsquare y] at hy
  exact ⟨(hag y hy).1, by simpa only [Function.comp_apply, hsquare] using (hag y hy).2⟩

variable [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Package an existing endpoint's actual carrier diffeomorphism.
Full tangent bijectivity follows from the compact atlas immersion;
the exterior derivative identity follows from native exterior naturality.
Only the already produced coordinate extensions are retained as data. -/
def NativeLiouvillePresentation.of_endpoint
    (α : Form k M 1) (D : LiouvilleDomain (k + 1))
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.domain.Point ∞)
    (hprimitive : ∀ x, (D.liouville.primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (fun y => (e y).val) x) = α x)
    (hcoordinates : HasNativeCoordinateExtensions (k := k) D.domain.extension (fun x => (e x).val)) :
    NativeLiouvillePresentation α := by
  let i : M → D.domain.extension.Point := fun x => (e x).val
  have hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i :=
    D.domain.contMDiff_subtype_val.comp e.contMDiff
  have hbij (x : M) : Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) := by
    have hd := mfderiv_comp (f := e) (g := (Subtype.val : D.domain.Point →
      D.domain.extension.Point)) x
      (D.domain.contMDiff_subtype_val.mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))
    change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x = _ at hd
    rw [hd]
    have h := (D.domain.injective_mfderiv_subtype_val (e x)).comp
      ((e.isInvertible_mfderiv (by simp)).injective)
    exact ⟨h, LinearMap.injective_iff_surjective.mp h⟩
  have hp : (fun x => (D.liouville.primitive (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α := funext hprimitive
  have hd := exteriorDerivative_pullback_from_boundaryless D.domain.extension i hi
    D.liouville.primitive D.liouville.smooth_primitive
  rw [hp] at hd
  refine
    { domain := D
      inclusion := i
      carrierEquiv := e
      carrier_square := fun _ => rfl
      smooth_inclusion := hi
      embedding := ?_
      tangent_bijective := hbij
      carrier_range := ?_
      primitive := hp
      differential := hd.symm
      coordinates := hcoordinates }
  · exact (D.domain.compact.isClosed.isClosedEmbedding_subtypeVal).comp
      e.toHomeomorph.isClosedEmbedding
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hy
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      exact ⟨x, congrArg Subtype.val hx⟩

@[simp] theorem NativeLiouvillePresentation.of_endpoint_domain
    (α : Form k M 1) (D : LiouvilleDomain (k + 1))
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.domain.Point ∞)
    (hp hc) : (NativeLiouvillePresentation.of_endpoint α D e hp hc).domain = D := rfl

@[simp] theorem NativeLiouvillePresentation.of_endpoint_inclusion
    (α : Form k M 1) (D : LiouvilleDomain (k + 1))
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.domain.Point ∞)
    (hp hc) (x : M) :
    (NativeLiouvillePresentation.of_endpoint α D e hp hc).inclusion x = (e x).val := rfl

end FsFltz.Geometry.IntrinsicLiouville
