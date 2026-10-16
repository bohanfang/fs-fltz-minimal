import FsFltz.Analysis.OriginalFiberDomain
import FsFltz.Analysis.OriginalRoundedDomain
import FsFltz.Geometry.DomainCompletionRestriction
import FsFltz.Geometry.PairFamilyConstruction
import FsFltz.Geometry.SmoothEmbeddingFactorization

/-!
# The actual original ribbon in the rounded boundary

Source: `geoemtric-part-fsf.tex`, `eq:initialpair`, lines 302–307,
the unchanged-face primitive identity, lines 341–348, and `g:initial`,
lines 370–384; `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines
923–930. The compact fiber presentation is restricted to the actual open
neighborhood untouched by rounding. Its inclusion factors smoothly through
the constructed rounded boundary, retaining the entire literal ribbon,
its original primitive, and its inclusion-induced full-fiber marking.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false

section Original

variable {n : ℕ} (I : ToricInput n) {Aamb R : ℝ}
  (hamb : AmbientEndBound I Aamb)
  (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)

local notation "F" => originalFullFiberModel I hamb hR

/-- Constancy of `W` on the actual whole far fiber kills the plane-form
summand, so the original ambient primitive restricts exactly to its given
intrinsic primitive, for every real `K`. -/
theorem pullback_lambdaK_originalFullFiber (K : ℝ) :
    (F).ambient.manifold.pullback (lgManifold n) (F).embedding.map
      (lambdaKForm I K) = (F).ambient.primitive := by
  rw [← (F).primitive]
  funext x
  ext vs
  have hz : complexDifferential (lgManifold n) (W I) ((F).embedding.map x)
      ((mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n))
        (F).embedding.map x) (vs 0)) = 0 := by
    have hm : (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n))
        (F).embedding.map x) (vs 0) ∈
        (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n))
          (F).embedding.map x).range := ⟨vs 0, rfl⟩
    rw [original_farFiber_embedding_tangent_range I hamb hR (F).embedding (F).image x] at hm
    exact hm
  simp [SmoothManifold.pullback, lambdaKForm, superpotentialPlaneForm, covectorForm, hz]

variable {Afib Aminus A : ℝ} (hfib : FiberEndBound I Aamb R Afib)
  (hAminus : Afib < Aminus) (m : RoundingChoice)
  (hpos : 0 < m.eps) (hwidth : m.eps < A - Aminus)

local notation "D" => originalFiberLiouvilleDomain I hamb hR hfib hAminus

/-- The inverse image in the actual full fiber of an actual open
neighborhood on which the rounding leaves the base face unchanged. -/
def originalRibbonNeighborhood : TopologicalSpace.Opens (F).ambient.manifold.Point :=
  let H := exists_unchanged_initialRibbon_neighborhood I R Aminus A m hpos hwidth
  ⟨(F).embedding.map ⁻¹' H.choose,
    H.choose_spec.1.preimage (F).embedding.map.contMDiff.continuous⟩

/-- The whole compact fiber carrier lies in the unchanged neighborhood. -/
theorem originalFiber_carrier_subset_ribbonNeighborhood :
    (D).domain.carrier ⊆
      (originalRibbonNeighborhood I hamb hR m hpos hwidth : Set (F).ambient.manifold.Point) := by
  intro x hx
  have hmem : (F).embedding.map x ∈ InitialRibbon I R Aminus := by
    rw [← originalFiberLiouvilleDomain_image I hamb hR hfib hAminus]
    exact ⟨x, hx, rfl⟩
  exact (exists_unchanged_initialRibbon_neighborhood I R Aminus A m hpos hwidth).choose_spec.2.1 hmem

/-- The entire restricted fiber extension lies on the rounded zero level. -/
theorem roundedDefiningFunction_originalRibbonNeighborhood
    (x : originalRibbonNeighborhood I hamb hR m hpos hwidth) :
    roundedDefiningFunction I R A m ((F).embedding.map x.val) = 0 := by
  have he := (exists_unchanged_initialRibbon_neighborhood I R Aminus A m hpos hwidth).choose_spec.2.2
    x.property
  have hw : W I ((F).embedding.map x.val) = (R : ℂ) := by
    have hh : (F).embedding.map x.val ∈ range (F).embedding.map := ⟨x.val, rfl⟩
    rwa [(F).image] at hh
  rw [he]
  change Complex.normSq (W I ((F).embedding.map x.val)) - R ^ 2 = 0
  rw [hw, Complex.normSq_ofReal]
  ring

/-- The actual ribbon Liouville domain, with its extension restricted
around the entire literal compact carrier. -/
abbrev originalRibbonLiouvilleDomain : LiouvilleDomain (2 * n - 2) :=
  (D).restrict (originalRibbonNeighborhood I hamb hR m hpos hwidth)
    (originalFiber_carrier_subset_ribbonNeighborhood I hamb hR hfib hAminus m hpos hwidth)

/-- The actual smooth inclusion of the ribbon extension into the same
specified full-fiber model. -/
def originalRibbonInFiber :
    (originalRibbonLiouvilleDomain I hamb hR hfib hAminus m hpos hwidth).domain.extension.SmoothEmbedding
      (F).ambient.manifold :=
  (F).ambient.manifold.restrictInclusion (originalRibbonNeighborhood I hamb hR m hpos hwidth)

local notation "U" => originalRibbonNeighborhood I hamb hR m hpos hwidth
local notation "hU" => originalFiber_carrier_subset_ribbonNeighborhood I hamb hR hfib hAminus m hpos hwidth
local notation "Dr" => originalRibbonLiouvilleDomain I hamb hR hfib hAminus m hpos hwidth

/-- The actual ambient inclusion of the restricted ribbon extension. -/
def originalRibbonInAmbient : (Dr).domain.extension.SmoothEmbedding (lgManifold n) :=
  (F).embedding.comp (originalRibbonInFiber I hamb hR hfib hAminus m hpos hwidth)

/-- The ribbon image is the entire literal original truncation. -/
theorem originalRibbonLiouvilleDomain_image :
    (originalRibbonInAmbient I hamb hR hfib hAminus m hpos hwidth).map ''
      (Dr).domain.carrier = InitialRibbon I R Aminus := by
  change ((F).embedding.map ∘ (Subtype.val : U → (F).ambient.manifold.Point)) ''
    (Subtype.val ⁻¹' (D).domain.carrier) = _
  rw [image_comp]
  erw [(D).domain.image_restrict_carrier U hU]
  exact originalFiberLiouvilleDomain_image I hamb hR hfib hAminus

/-- Restricting the extension preserves the nonempty entire compact ribbon. -/
theorem originalRibbonLiouvilleDomain_nonempty : (Dr).domain.carrier.Nonempty := by
  obtain ⟨x, hx⟩ := originalFiberLiouvilleDomain_nonempty I hamb hR hfib hAminus
  exact ⟨⟨x, hU hx⟩, hx⟩

/-- The ribbon primitive is literally the pullback of the prescribed
original ambient primitive on the whole restricted extension. -/
theorem pullback_lambdaK_originalRibbon (K : ℝ) :
    (Dr).domain.extension.pullback (lgManifold n)
      (originalRibbonInAmbient I hamb hR hfib hAminus m hpos hwidth).map
      (lambdaKForm I K) = (Dr).liouville.primitive := by
  funext x
  change ((F).ambient.manifold.restrict U).pullback (lgManifold n)
    (fun y : U => (F).embedding.map y.val) (lambdaKForm I K) x = _
  rw [(F).ambient.manifold.pullback_comp_restrict_val (lgManifold n) U
    (F).embedding.map (lambdaKForm I K) x, pullback_lambdaK_originalFullFiber I hamb hR]
  exact ((D).liouville.restrict_primitive U hU x).symm

/-- The actual completion retains the whole specified full-fiber ambient
and its original complete intrinsic flow after extension restriction. -/
def originalRibbonCompletion : Completion (Dr) :=
  (originalFiberCompletion I hamb hR hfib hAminus).restrict U hU

/-- The actual inclusion-induced marking onto the full original fiber,
with its prescribed all-real-time flow equation. -/
def originalRibbonInclusionMarking :
    InclusionMarking (originalRibbonCompletion I hamb hR hfib hAminus m hpos hwidth)
      (F).ambient
      (fun x => (originalRibbonInFiber I hamb hR hfib hAminus m hpos hwidth).map x.val) :=
  (originalFiberCompletion I hamb hR hfib hAminus).restrictInclusionMarking U hU
    (F).ambient (fun x => x.val) (originalFiberInclusionMarking I hamb hR hfib hAminus)

variable {K : ℝ} (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
  (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)

local notation "E" => originalRoundedLiouvilleDomain I hamb hR hset hK hfib hAminus m hadmiss

/-- The actual ribbon extension embeds smoothly in the actual rounded
boundary. Its full extension square commutes in the original ambient, and
its pullback primitive is exactly the prescribed intrinsic primitive.
The topology, atlas and immersion of this factor are proved, not supplied. -/
theorem exists_originalRibbonBoundaryEmbedding :
    ∃ j : (Dr).domain.extension.SmoothEmbedding (E).domain.boundary,
      (∀ x, (E).domain.boundaryInclusion.map (j.map x) =
        (originalRibbonInAmbient I hamb hR hfib hAminus m hpos hwidth).map x) ∧
      (Dr).domain.extension.pullback (E).domain.boundary j.map
        ((E).domain.boundaryForm (E).liouville.primitive) = (Dr).liouville.primitive := by
  let g := originalRibbonInAmbient I hamb hR hfib hAminus m hpos hwidth
  have hrange : range g.map ⊆ range (E).domain.boundaryInclusion.map := by
    rintro y ⟨x, rfl⟩
    rw [originalRoundedCompactDomain_boundary_range I hamb hR hset hK hfib hAminus m hadmiss]
    exact roundedDefiningFunction_originalRibbonNeighborhood I hamb hR m hpos hwidth x
  obtain ⟨j, hj⟩ := exists_smoothEmbedding_factor (E).domain.boundary (Dr).domain.extension
    (lgManifold n) (E).domain.boundaryInclusion g hrange
  refine ⟨j, hj, ?_⟩
  change (Dr).domain.extension.pullback (E).domain.boundary j.map
    ((E).domain.boundary.pullback (lgManifold n) (E).domain.boundaryInclusion.map
      (lambdaKForm I K)) = (Dr).liouville.primitive
  rw [← (Dr).domain.extension.pullback_comp (E).domain.boundary (lgManifold n)
    (j.map.contMDiff.mdifferentiable (by simp))
    ((E).domain.boundaryInclusion.map.contMDiff.mdifferentiable (by simp))]
  have he : (E).domain.boundaryInclusion.map ∘ j.map = g.map := funext hj
  rw [he]
  exact pullback_lambdaK_originalRibbon I hamb hR hfib hAminus m hpos hwidth K

end Original

end FsFltz.Geometry
