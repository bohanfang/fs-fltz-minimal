import FsFltz.Geometry.OriginalVaryingLevelCompletion

/-!
# Actual original initial pairs throughout the varying full-ribbon family

Source: `geoemtric-part-fsf.tex`, `lem:choices`, lines 448–474, and
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 956–973. The common
rounded ambient is unchanged. Every slice retains its whole literal ribbon
and both original inclusion/flow completion markings.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.InitialPairData

/-- Relabel an equal ribbon level without changing any actual pair data. -/
def castRibbonLevel {n : ℕ} {I : ToricInput n} {R K A B Elevel : ℝ} {m : RoundingChoice}
    (h : A = B) (S : InitialPairData I R K A Elevel m) :
    InitialPairData I R K B Elevel m :=
  { S with ribbon_image := by rw [← h]; exact S.ribbon_image }

@[simp] theorem castRibbonLevel_pair {n : ℕ} {I : ToricInput n}
    {R K A B Elevel : ℝ} {m : RoundingChoice} (h : A = B)
    (S : InitialPairData I R K A Elevel m) : (S.castRibbonLevel h).pair = S.pair := rfl

end FsFltz.InitialPairData

namespace FsFltz.Geometry
open SmoothManifold

section Original
variable {n : ℕ} (I : ToricInput n) {Aamb R Afib K A B Lbound Elevel : ℝ}
  (hamb : AmbientEndBound I Aamb)
  (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
  (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
  (hfib : FiberEndBound I Aamb R Afib) (hA : Afib < A) (hB : Afib < B)
  (hL : max A B < Lbound) (m : RoundingChoice)
  (hm : GeometricAdmissibleRounding I R K Lbound Elevel m)

local notation "F" => originalFullFiberModel I hamb hR
local notation "η" => (phi0 ∘ SmoothEmbedding.map
  (FullFiberModel.embedding (originalFullFiberModel I hamb hR)))
local notation "hLb" => lt_trans hA (lt_of_le_of_lt (le_max_left A B) hL)
local notation "E" => originalRoundedLiouvilleDomain I hamb hR hset hK hfib hLb m hm
local notation "CE" => originalRoundedCompletion I hamb hR hset hK hfib hLb m hm

/-- Native boundary-family data, with every primitive, image and map
equation explicit. Its completion family will be constructed, not stored
as a hypothesis. -/
structure OriginalVaryingLevelBoundaryData where
  domain : CompactDomain (2 * n - 2)
  fiberEmbedding : Parameter → domain.extension.SmoothEmbedding (F).ambient.manifold
  boundaryEmbedding : Parameter → domain.extension.SmoothEmbedding (E).domain.boundary
  liouville : Parameter → LiouvilleStructure domain
  nonempty : domain.carrier.Nonempty
  fiber_smooth : domain.extension.IsSmoothIntervalMapFamily (F).ambient.manifold
    (fun t => (fiberEmbedding t).map)
  boundary_smooth : domain.extension.IsSmoothIntervalMapFamily (E).domain.boundary
    (fun t => (boundaryEmbedding t).map)
  square : ∀ t x, (E).domain.boundaryInclusion.map ((boundaryEmbedding t).map x) =
    (F).embedding.map ((fiberEmbedding t).map x)
  carrier_image : ∀ t : Parameter, (fiberEmbedding t).map '' domain.carrier =
    {x | η x ≤ (1 - t.val) * A + t.val * B}
  frontier_image : ∀ t : Parameter, (fiberEmbedding t).map '' frontier domain.carrier =
    {x | η x = (1 - t.val) * A + t.val * B}
  ambient_ribbon_image : ∀ t : Parameter,
    ((F).embedding.comp (fiberEmbedding t)).map '' domain.carrier =
      InitialRibbon I R ((1 - t.val) * A + t.val * B)
  primitive : ∀ t, (liouville t).primitive = domain.extension.pullback
    (F).ambient.manifold (fiberEmbedding t).map (F).ambient.primitive
  primitive_smooth : domain.extension.IsSmoothIntervalFormFamily (fun t => (liouville t).primitive)
  boundary_primitive : ∀ t, domain.extension.pullback (E).domain.boundary
    (boundaryEmbedding t).map ((E).domain.boundaryForm (E).liouville.primitive) =
      (liouville t).primitive

namespace OriginalVaryingLevelBoundaryData
variable {I} {hamb} {hR} {hset} {hK} {hfib} {hA} {hB} {hL} {m} {hm}
variable (V : OriginalVaryingLevelBoundaryData I hamb hR hset hK hfib hA hL m hm)

/-- Construct the actual ribbon completion family from its smooth native
primitive family. -/
def ribbonFamily : LocalizedCompletionFamily V.domain V.liouville :=
  V.domain.localizedCompletionFamily V.liouville V.primitive_smooth

/-- The same completed witnessed pair deformation, with original ambient
domain and original ambient completion literally constant. -/
def deformation : PairDeformation n :=
  fixedAmbientLocalizedPairDeformation (E) (CE) V.domain V.liouville V.boundaryEmbedding
    V.boundary_smooth V.ribbonFamily V.boundary_primitive

include hA hB in
private theorem level_above_bound (t : Parameter) :
    Afib < (1 - t.val) * A + t.val * B := by
  have h0 := t.property.1
  have h1 := t.property.2
  have he : min A B ≤ (1 - t.val) * A + t.val * B := by
    calc
      min A B = (1 - t.val) * min A B + t.val * min A B := by ring
      _ ≤ (1 - t.val) * A + t.val * B := by gcongr <;> simp
  exact (lt_min hA hB).trans_le he

/-- Every slice is actual original initial-pair data at its literal level,
including the full-fiber marking of the completion constructed above. -/
def initial (hB : Afib < B) (t : Parameter) :
    InitialPairData I R K ((1 - t.val) * A + t.val * B) Elevel m := by
  let Bc := V.ribbonFamily.collars t
  let P := V.deformation.pair t
  let J := (V.fiberEmbedding t).comp Bc.originalInclusion
  have hc : J.map '' Bc.localizedDomain.domain.carrier =
      {x | η x ≤ (1 - t.val) * A + t.val * B} := by
    change ((V.fiberEmbedding t).map ∘ Bc.originalInclusion.map) '' _ = _
    rw [image_comp, Bc.image_originalInclusion_carrier, V.carrier_image]
  have hne : Bc.localizedDomain.domain.carrier.Nonempty := by
    have he := Bc.image_originalInclusion_carrier
    have hne₀ := V.nonempty
    rw [← he] at hne₀
    exact hne₀.of_image
  have hp : ∀ x ∈ Bc.localizedDomain.domain.carrier,
      Bc.localizedDomain.liouville.primitive x =
        Bc.localizedDomain.domain.extension.pullback (F).ambient.manifold J.map
          (F).ambient.primitive x := by
    intro x _
    rw [Bc.original_primitive, V.primitive]
    change V.domain.extension.pullback (F).ambient.manifold (V.fiberEmbedding t).map _ x.val.val = _
    change _ = Bc.localizedDomain.domain.extension.pullback (F).ambient.manifold
      ((V.fiberEmbedding t).map ∘ Bc.originalInclusion.map) (F).ambient.primitive x
    rw [Bc.localizedDomain.domain.extension.pullback_comp V.domain.extension (F).ambient.manifold
      (Bc.originalInclusion.map.contMDiff.mdifferentiable (by simp))
      ((V.fiberEmbedding t).map.contMDiff.mdifferentiable (by simp)), Bc.pullback_originalInclusion]
  let marking := Classical.choice (exists_originalSublevelPresentation_fiberMarking I hamb hR hfib
    (level_above_bound (hA := hA) (hB := hB) t)
    Bc.localizedDomain Bc.cylindricalCompletion hne J hc hp)
  exact
    { pair := P
      ambient := originalCompletePrimitive I
        ((zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK)
      domainEmbedding := SmoothEmbedding.identity (lgManifold n)
      domain_image := by exact image_id _
      ambientMarking := originalRoundedInclusionMarking I hamb hR hset hK hfib hLb m hm (CE)
      witness_one := fun _ => rfl
      fiber := F
      ribbonInFiber := J
      ribbon_image := by
        change (((F).embedding.comp (V.fiberEmbedding t)).map ∘ Bc.originalInclusion.map) ''
          Bc.localizedDomain.domain.carrier = _
        rw [image_comp, Bc.image_originalInclusion_carrier]
        exact V.ambient_ribbon_image t
      ribbon_square := fun x _ => V.square t (Bc.originalInclusion.map x)
      fiberMarking := marking
      ribbon_nonempty := hne }

@[simp] theorem initial_pair (t : Parameter) : (V.initial hB t).pair = V.deformation.pair t := rfl

/-- The actual marking of this same completed deformation is constant on
the entire ambient manifold and jointly smooth in both specified native
presentations. -/
def fixedAmbientDeformation (hB : Afib < B) :
    FixedAmbientPairDeformation V.deformation
      (V.initial hB parameterZero).fixedAmbientMarking
      (V.initial hB parameterOne).fixedAmbientMarking where
  marking := fun t => (V.initial hB t).fixedAmbientMarking
  source_eq := rfl
  target_eq := rfl
  completed_smooth := by
    change (CE).ambient.manifold.IsSmoothIntervalMapFamily (lgManifold n)
      (fun (_ : Parameter) x =>
        (originalRoundedInclusionMarking I hamb hR hset hK hfib hLb m hm (CE)).equiv x)
    exact (CE).ambient.manifold.isSmoothIntervalMapFamily_constant (lgManifold n) _
      (originalRoundedInclusionMarking I hamb hR hset hK hfib hLb m hm (CE)).equiv.contMDiff
  compact_smooth := by
    change (E).domain.extension.IsSmoothIntervalMapFamily (lgManifold n)
      (fun (_ : Parameter) x => x)
    exact (E).domain.extension.isSmoothIntervalMapFamily_constant (lgManifold n) id contMDiff_id

end OriginalVaryingLevelBoundaryData

include hB in
/-- The full transverse motion constructs the explicit native boundary
data from arbitrary valid fiber bounds, both levels and every chosen
admissible common rounded domain. -/
theorem nonempty_originalVaryingLevelBoundaryData :
    Nonempty (OriginalVaryingLevelBoundaryData I hamb hR hset hK hfib hA hL m hm) := by
  obtain ⟨D, J, j, Λ, hD, hJ, hj, hsquare, himages, hp, hps, hbp⟩ :=
    exists_originalVaryingLevel_boundaryLiouvilleFamily I hamb hR hset hK hfib hA hB hL m hm
  exact ⟨{
    domain := D
    fiberEmbedding := J
    boundaryEmbedding := j
    liouville := Λ
    nonempty := hD
    fiber_smooth := hJ
    boundary_smooth := hj
    square := hsquare
    carrier_image := fun t => (himages t).1
    frontier_image := fun t => (himages t).2.1
    ambient_ribbon_image := fun t => (himages t).2.2
    primitive := hp
    primitive_smooth := hps
    boundary_primitive := hbp }⟩

end Original
end FsFltz.Geometry
