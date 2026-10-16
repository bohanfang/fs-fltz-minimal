import FsFltz.Geometry.OriginalVaryingLevelFace
import FsFltz.Geometry.PairGermFamilyConstruction
import FsFltz.Geometry.PotentialPathRoundedMarking

/-!
# The actual varying-level ribbon family in one original rounded boundary

Source: `geoemtric-part-fsf.tex`, `lem:choices`, lines 448–473, and
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 956–972. The actual
transverse ribbon motion is restricted to one unchanged base face, and its
primitive remains the restriction of the original ambient primitive. Both
compact image equations hold on the same native smooth family used by the
subsequent completion construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Function

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

/-- Postcomposition by one fixed smooth map retains actual interval-map
extensions. -/
theorem IsSmoothIntervalMapFamily.postcomp {d e f : ℕ}
    {M : SmoothManifold d} {N : SmoothManifold e} {P : SmoothManifold f}
    {J : Parameter → M.Point → N.Point} (hJ : M.IsSmoothIntervalMapFamily N J)
    (g : N.Point → P.Point) (hg : ContMDiff 𝓘(ℝ, Model e) 𝓘(ℝ, Model f) ∞ g) :
    M.IsSmoothIntervalMapFamily P (fun t x => g (J t x)) := by
  obtain ⟨j, ⟨U, hU, hcover, hs⟩, he⟩ := hJ
  refine ⟨fun t x => g (j t x), ⟨U, hU, hcover, hg.comp_contMDiffOn hs⟩, ?_⟩
  intro t
  funext x
  exact congrArg g (congrFun (he t) x)

end SmoothManifold

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

include hA hB hL

private theorem level_below_common (t : Parameter) :
    Afib < (1 - t.val) * A + t.val * B ∧
      (1 - t.val) * A + t.val * B < Lbound := by
  have h0 := t.property.1
  have h1 := t.property.2
  constructor
  · have hmin : min A B ≤ (1 - t.val) * A + t.val * B := by
      calc
        min A B = (1 - t.val) * min A B + t.val * min A B := by ring
        _ ≤ (1 - t.val) * A + t.val * B := by gcongr <;> simp
    exact (lt_min hA hB).trans_le hmin
  · apply lt_of_le_of_lt _ hL
    calc
      (1 - t.val) * A + t.val * B ≤ (1 - t.val) * max A B + t.val * max A B := by
        gcongr <;> simp
      _ = max A B := by ring

include hamb hR hset hK hfib hm

/-- The actual varying full ribbons lie in one unchanged rounded boundary.
One fixed carrier carries their actual primitives and native Liouville
structures; all carrier and boundary images retain the original equations. -/
theorem exists_originalVaryingLevel_boundaryLiouvilleFamily :
    let hLb : Afib < Lbound := hA.trans ((le_max_left A B).trans_lt hL)
    let E := originalRoundedLiouvilleDomain I hamb hR hset hK hfib hLb m hm
    ∃ (D : CompactDomain (2 * n - 2))
      (J : Parameter → D.extension.SmoothEmbedding (F).ambient.manifold)
      (j : Parameter → D.extension.SmoothEmbedding E.domain.boundary)
      (Λ : Parameter → LiouvilleStructure D),
      D.carrier.Nonempty ∧
      D.extension.IsSmoothIntervalMapFamily (F).ambient.manifold (fun t => (J t).map) ∧
      D.extension.IsSmoothIntervalMapFamily E.domain.boundary (fun t => (j t).map) ∧
      (∀ t x, E.domain.boundaryInclusion.map ((j t).map x) = (F).embedding.map ((J t).map x)) ∧
      (∀ t : Parameter,
        (J t).map '' D.carrier = {x | η x ≤ (1 - t.val) * A + t.val * B} ∧
        (J t).map '' frontier D.carrier = {x | η x = (1 - t.val) * A + t.val * B} ∧
        ((F).embedding.comp (J t)).map '' D.carrier =
          InitialRibbon I R ((1 - t.val) * A + t.val * B)) ∧
      (∀ t, (Λ t).primitive = D.extension.pullback (F).ambient.manifold (J t).map
        (F).ambient.primitive) ∧
      D.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) ∧
      (∀ t, D.extension.pullback E.domain.boundary (j t).map
        (E.domain.boundaryForm E.liouville.primitive) = (Λ t).primitive) := by
  let hLb : Afib < Lbound := hA.trans ((le_max_left A B).trans_lt hL)
  let E := originalRoundedLiouvilleDomain I hamb hR hset hK hfib hLb m hm
  let O := originalRibbonNeighborhood I hamb hR m hm.1 hm.2.1
  obtain ⟨j₀, hj₀, hp₀⟩ := exists_originalRibbonBoundaryEmbedding I hamb hR hfib hLb m
    hm.1 hm.2.1 hset hK hm
  obtain ⟨D₀, J₀, Λ₀, hD₀, hJ₀, himages, hprimitive, hs, _hz, _hc⟩ :=
    exists_originalVaryingLevel_liouvilleFamily I hamb hR hfib hA hB
  have hO : ∀ t x, x ∈ D₀.carrier → (J₀ t).map x ∈ O := by
    intro t x hx
    apply originalFiber_carrier_subset_ribbonNeighborhood I hamb hR hfib hLb m hm.1 hm.2.1
    rw [originalFiberLiouvilleDomain_carrier I hamb hR hfib hLb]
    have hh : (J₀ t).map x ∈ (J₀ t).map '' D₀.carrier := ⟨x, hx, rfl⟩
    rw [(himages t).1] at hh
    exact hh.trans (level_below_common hA hB hL t).2.le
  obtain ⟨U, hDU, Kt, hformula, hKt⟩ := D₀.exists_embeddingFamily_into_open
    (F).ambient.manifold J₀ hJ₀ O hO
  let D := D₀.restrict U hDU
  let J : Parameter → D.extension.SmoothEmbedding (F).ambient.manifold :=
    fun t => ((F).ambient.manifold.restrictInclusion O).comp (Kt t)
  let j : Parameter → D.extension.SmoothEmbedding E.domain.boundary := fun t => j₀.comp (Kt t)
  let Λ : Parameter → LiouvilleStructure D := fun t => (Λ₀ t).restrict U hDU
  have hJ : D.extension.IsSmoothIntervalMapFamily (F).ambient.manifold (fun t => (J t).map) :=
    hKt.postcomp ((F).ambient.manifold.restrictInclusion O).map
      ((F).ambient.manifold.restrictInclusion O).map.contMDiff
  have hj : D.extension.IsSmoothIntervalMapFamily E.domain.boundary (fun t => (j t).map) :=
    hKt.postcomp j₀.map j₀.map.contMDiff
  have hJformula (t : Parameter) (x : D.extension.Point) : (J t).map x = (J₀ t).map x.val :=
    hformula t x
  have hΛ (t : Parameter) : (Λ t).primitive =
      D.extension.pullback (F).ambient.manifold (J t).map (F).ambient.primitive := by
    funext x
    rw [(Λ₀ t).restrict_primitive U hDU, hprimitive]
    change D₀.extension.pullback (F).ambient.manifold (J₀ t).map (F).ambient.primitive x.val = _
    rw [show (J t).map = (J₀ t).map ∘ (Subtype.val : U → D₀.extension.Point) from funext (hJformula t)]
    exact (D₀.extension.pullback_comp_restrict_val (F).ambient.manifold U (J₀ t).map _ x).symm
  have hΛs : D.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) := by
    have he : (fun t => (Λ t).primitive) =
        (fun t => D.extension.pullback D₀.extension Subtype.val (Λ₀ t).primitive) := by
      funext t x
      rw [(Λ₀ t).restrict_primitive U hDU, D₀.extension.pullback_restrict_val]
    rw [he]
    exact D₀.extension.isSmoothIntervalFormFamily_restrict U _ hs
  have hD : D.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hD₀
    exact ⟨⟨x, hDU hx⟩, hx⟩
  refine ⟨D, J, j, Λ, hD, hJ, hj, ?_, ?_, hΛ, hΛs, ?_⟩
  · intro t x
    exact hj₀ ((Kt t).map x)
  · intro t
    have hc : (J t).map '' D.carrier = (J₀ t).map '' D₀.carrier := by
      rw [show (J t).map = (J₀ t).map ∘ (Subtype.val : U → D₀.extension.Point) from funext (hJformula t),
        image_comp, D₀.image_restrict_carrier U hDU]
    have hb : (J t).map '' frontier D.carrier = (J₀ t).map '' frontier D₀.carrier := by
      rw [show (J t).map = (J₀ t).map ∘ (Subtype.val : U → D₀.extension.Point) from funext (hJformula t),
        image_comp, D₀.frontier_restrict_carrier U]
      have he : Subtype.val '' (Subtype.val ⁻¹' frontier D₀.carrier : Set U) = frontier D₀.carrier :=
        image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hDU (D₀.compact.isClosed.frontier_subset hx)⟩, rfl⟩)
      rw [he]
    refine ⟨hc.trans (himages t).1, hb.trans (himages t).2.1, ?_⟩
    change ((F).embedding.map ∘ (J t).map) '' D.carrier = _
    rw [image_comp, hc]
    rw [← image_comp]
    exact (himages t).2.2
  · intro t
    change D.extension.pullback E.domain.boundary (j₀.map ∘ (Kt t).map) _ = _
    rw [D.extension.pullback_comp ((F).ambient.manifold.restrict O) E.domain.boundary
      ((Kt t).map.contMDiff.mdifferentiable (by simp)) (j₀.map.contMDiff.mdifferentiable (by simp))]
    have hp₀' : ((F).ambient.manifold.restrict O).pullback E.domain.boundary j₀.map
        (E.domain.boundaryForm E.liouville.primitive) =
          (originalRibbonLiouvilleDomain I hamb hR hfib hLb m hm.1 hm.2.1).liouville.primitive := hp₀
    rw [hp₀', hΛ]
    change D.extension.pullback ((F).ambient.manifold.restrict O) (Kt t).map
      (originalRibbonLiouvilleDomain I hamb hR hfib hLb m hm.1 hm.2.1).liouville.primitive = _
    have ho : (originalRibbonLiouvilleDomain I hamb hR hfib hLb m hm.1 hm.2.1).liouville.primitive =
        ((F).ambient.manifold.restrict O).pullback (F).ambient.manifold Subtype.val (F).ambient.primitive := by
      funext x
      rw [(originalFiberLiouvilleDomain I hamb hR hfib hLb).liouville.restrict_primitive]
      rw [(F).ambient.manifold.pullback_restrict_val]
      rfl
    rw [ho]
    exact (D.extension.pullback_comp ((F).ambient.manifold.restrict O) (F).ambient.manifold
      (u := (Kt t).map) (v := (Subtype.val : O → (F).ambient.manifold.Point))
      ((Kt t).map.contMDiff.mdifferentiable (by simp))
      (((F).ambient.manifold.restrictInclusion O).map.contMDiff.mdifferentiable (by simp))
      (F).ambient.primitive).symm

end Original
end FsFltz.Geometry
