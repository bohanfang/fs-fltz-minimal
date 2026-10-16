import FsFltz.Geometry.OriginalRibbonLevelTransport
import FsFltz.Geometry.MarkedFlowEmbedding
import FsFltz.Geometry.CompactDomainLiouvillePullback
import FsFltz.Geometry.OriginalParameterPairFamily
import FsFltz.Geometry.TailoringRoundedPairCarrier

/-!
# Actual full original ribbon families with arbitrary varying levels

Source: `geoemtric-part-fsf.tex`, `lem:choices`, lines 448–469, and
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 956–971. The original
full-fiber transverse motion constructs a common compact carrier and its
actual pulled-back intrinsic Liouville and completion family. No comparison
chain or ribbon motion is an input. Arbitrary valid bounds and levels,
including rank one, are retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Function

namespace FsFltz.Geometry
open SmoothManifold

section Original
variable {n : ℕ} (I : ToricInput n) {Aamb R Afib A B : ℝ}
  (hamb : AmbientEndBound I Aamb)
  (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
  (hfib : FiberEndBound I Aamb R Afib) (hA : Afib < A) (hB : Afib < B)

local notation "F" => originalFullFiberModel I hamb hR
local notation "η" => (phi0 ∘ SmoothEmbedding.map
  (FullFiberModel.embedding (originalFullFiberModel I hamb hR)))

include hfib hA hB

/-- The actual entire original ribbons at all affine levels have a single
nonempty compact carrier and jointly smooth embeddings into the actual full
fiber. Native boundary images and every component are retained literally. -/
theorem exists_originalVaryingLevel_fixedCarrier_embeddings :
    ∃ (D : CompactDomain (2 * n - 2))
      (J : Parameter → D.extension.SmoothEmbedding (F).ambient.manifold),
      D.carrier.Nonempty ∧
      D.extension.IsSmoothIntervalMapFamily (F).ambient.manifold (fun t => (J t).map) ∧
      ∀ t : Parameter,
        (J t).map '' D.carrier = {x | η x ≤ (1 - t.val) * A + t.val * B} ∧
        (J t).map '' frontier D.carrier = {x | η x = (1 - t.val) * A + t.val * B} ∧
        ((F).embedding.comp (J t)).map '' D.carrier =
          InitialRibbon I R ((1 - t.val) * A + t.val * B) := by
  let D₀ := (originalFiberLiouvilleDomain I hamb hR hfib hA).domain
  have hcarrier : D₀.carrier = {x | η x ≤ A} :=
    originalFiberLiouvilleDomain_carrier I hamb hR hfib hA
  have hfrontier : frontier D₀.carrier = {x | η x = A} :=
    originalFiberLiouvilleDomain_frontier I hamb hR hfib hA
  let : ChartedSpace (ℝ × Model (2 * n - 2)) (ℝ × (F).ambient.manifold.Point) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n - 2)))
      (ℝ × (F).ambient.manifold.Point))
  let : IsManifold 𝓘(ℝ, ℝ × Model (2 * n - 2)) ∞ (ℝ × (F).ambient.manifold.Point) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n - 2))) ∞
      (ℝ × (F).ambient.manifold.Point))
  obtain ⟨Φ, hΦ, hpres⟩ := exists_originalRibbonLevel_transport I hamb hR hfib hA hB
  have htime : ∀ t ∈ parameterInterval, ∀ x ∈ D₀.carrier, (Φ t (0, x)).1 = t := by
    intro t ht x hx
    have hxA : η x ≤ (1 - (0 : ℝ)) * A + 0 * B := by
      rw [hcarrier] at hx
      simpa only [sub_zero, one_mul, zero_mul, add_zero] using (show η x ≤ A from hx)
    simpa only [zero_add] using
      (hpres 0 (by constructor <;> norm_num) x hxA t
        (by simpa only [zero_add] using (show t ∈ Icc (0 : ℝ) 1 from ht))).1
  rw [modelWithCornersSelf_prod] at hΦ
  obtain ⟨U, hDU, J, hformula, hJ⟩ := exists_uniform_projectedFlow_embedding_neighborhood
    D₀ (F).ambient.manifold (SmoothEmbedding.identity _) Φ hΦ htime
  let D := D₀.restrict U hDU
  have hD : D.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := originalFiberLiouvilleDomain_nonempty I hamb hR hfib hA
    exact ⟨⟨x, hDU hx⟩, hx⟩
  refine ⟨D, J, hD, hJ, ?_⟩
  intro t
  obtain ⟨hsub, hboundary⟩ := (F).ambient.manifold.affine_sublevel_transport_images
    η A B Φ hpres (s := 0) (by constructor <;> norm_num) t.property
  have hsub' : (J t).map '' D.carrier = {x | η x ≤ (1 - t.val) * A + t.val * B} := by
    have he : (J t).map =
        (fun x => (Φ t.val (0, x)).2) ∘ (Subtype.val : U → D₀.extension.Point) := by
      funext x
      exact hformula t x
    rw [he, image_comp, D₀.image_restrict_carrier U hDU, hcarrier]
    simpa using hsub
  have hboundary' : (J t).map '' frontier D.carrier =
      {x | η x = (1 - t.val) * A + t.val * B} := by
    have he : (J t).map =
        (fun x => (Φ t.val (0, x)).2) ∘ (Subtype.val : U → D₀.extension.Point) := by
      funext x
      exact hformula t x
    rw [he, image_comp, D₀.frontier_restrict_carrier U]
    have hi : Subtype.val '' (Subtype.val ⁻¹' frontier D₀.carrier : Set U) = frontier D₀.carrier :=
      image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hDU (D₀.compact.isClosed.frontier_subset hx)⟩, rfl⟩)
    rw [hi, hfrontier]
    simpa using hboundary
  refine ⟨hsub', hboundary', ?_⟩
  change ((F).embedding.map ∘ (J t).map) '' D.carrier = _
  rw [image_comp, hsub']
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by have hm : (F).embedding.map x ∈ range (F).embedding.map := ⟨x, rfl⟩
              rwa [(F).image] at hm, hx⟩
  · rintro ⟨hy, hphi⟩
    have hm : y ∈ range (F).embedding.map := by rwa [(F).image]
    obtain ⟨x, rfl⟩ := hm
    exact ⟨x, hphi, rfl⟩

/-- The constructed common full-ribbon carrier has the actual intrinsic
Liouville primitive, outward field and constructed completed family at
every affine level. No family regularity or outwardness is assumed. -/
theorem exists_originalVaryingLevel_liouvilleFamily :
    ∃ (D : CompactDomain (2 * n - 2))
      (J : Parameter → D.extension.SmoothEmbedding (F).ambient.manifold)
      (L : Parameter → LiouvilleStructure D),
      D.carrier.Nonempty ∧
      D.extension.IsSmoothIntervalMapFamily (F).ambient.manifold (fun t => (J t).map) ∧
      (∀ t : Parameter,
        (J t).map '' D.carrier = {x | η x ≤ (1 - t.val) * A + t.val * B} ∧
        (J t).map '' frontier D.carrier = {x | η x = (1 - t.val) * A + t.val * B} ∧
        ((F).embedding.comp (J t)).map '' D.carrier =
          InitialRibbon I R ((1 - t.val) * A + t.val * B)) ∧
      (∀ t, (L t).primitive = D.extension.pullback (F).ambient.manifold (J t).map
        (F).ambient.primitive) ∧
      D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      D.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) ∧
      Nonempty (LocalizedCompletionFamily D L) := by
  obtain ⟨D, J, hD, hJ, himages⟩ :=
    exists_originalVaryingLevel_fixedCarrier_embeddings I hamb hR hfib hA hB
  let q : Parameter → (F).ambient.manifold.Point → ℝ :=
    fun t x => η x - ((1 - t.val) * A + t.val * B)
  have hq (t : Parameter) : ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞ (q t) :=
    (contMDiff_originalFullFiber_phi0 I hamb hR).sub_const _
  have hside : ∀ t x, x ∈ D.carrier → q t ((J t).map x) ≤ 0 := by
    intro t x hx
    have hm : (J t).map x ∈ (J t).map '' D.carrier := ⟨x, hx, rfl⟩
    rw [(himages t).1] at hm
    exact sub_nonpos.mpr hm
  have hzero : ∀ t x, x ∈ frontier D.carrier → q t ((J t).map x) = 0 := by
    intro t x hx
    have hm : (J t).map x ∈ (J t).map '' frontier D.carrier := ⟨x, hx, rfl⟩
    rw [(himages t).2.1] at hm
    exact sub_eq_zero.mpr hm
  have hout : ∀ t x, x ∈ frontier D.carrier →
      0 < (F).ambient.manifold.scalarDerivative (q t) ((J t).map x)
        ((F).ambient.manifold.liouvilleVector (F).ambient.primitive ((J t).map x)) := by
    intro t x hx
    have he := sub_eq_zero.mp (hzero t x hx)
    have hlevel : Afib < (1 - t.val) * A + t.val * B := by
      have hmin : min A B ≤ (1 - t.val) * A + t.val * B := by
        have ht0 := t.property.1
        have ht1 := t.property.2
        calc
          min A B = (1 - t.val) * min A B + t.val * min A B := by ring
          _ ≤ (1 - t.val) * A + t.val * B := by gcongr <;> simp
      exact (lt_min hA hB).trans_le hmin
    unfold scalarDerivative
    change 0 < (show ℝ from (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ)
      (η - fun _ => ((1 - t.val) * A + t.val * B)) ((J t).map x))
        ((F).ambient.manifold.liouvilleVector (F).ambient.primitive ((J t).map x)))
    rw [mfderiv_sub ((contMDiff_originalFullFiber_phi0 I hamb hR).mdifferentiableAt (by simp))
      mdifferentiableAt_const, mfderiv_const, sub_zero]
    exact scalarDerivative_originalFullFiber_phi0_pos I hamb hR hfib ((J t).map x)
      (by rw [he]; exact hlevel.le)
  obtain ⟨L, hp, hs, hz, _hω, hc, _hmap⟩ := D.exists_liouvilleFamily_of_sublevel_pullback
    (F).ambient.manifold J hJ (fun _ => (F).ambient.primitive)
    ((F).ambient.manifold.isSmoothIntervalFormFamily_constant _ (F).ambient.smooth_primitive)
    (fun _ y => (F).ambient.symplectic.2.2 y (mem_univ _)) q hq hside hzero hout
  exact ⟨D, J, L, hD, hJ, himages, hp, hs, hz, hc⟩

end Original
end FsFltz.Geometry
