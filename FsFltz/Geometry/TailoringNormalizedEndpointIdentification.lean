import FsFltz.Geometry.NativeCompactMapCompletion
import FsFltz.Geometry.IntrinsicNativePairIdentification
import FsFltz.Analysis.TailoringNormalization
import FsFltz.Geometry.CommonEmbeddingCompactMap
import FsFltz.Geometry.TailoringRoundedCompletionMarking
import FsFltz.Geometry.PairFamilyConstruction

/-!
# Strict comparison at a normalized compact-pair junction

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199;
`geometric-part-fsf-proof.tex`, `eq:normalizedrounding`, lines 1260–1262,
and the normalized junction, lines 1304–1314. Actual compact ambient and
ribbon maps extend to a permitted strict completion identification.
Their square is imposed on every ribbon point, not only on its core.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.CompletionIdentification
open SmoothManifold

/-- A strict compact ambient map and a constant-scale compact ribbon map
with their literal full-ribbon square construct a permitted identification
between the already chosen completions. Its actual end shift is zero. -/
theorem exists_of_compactPairSquare {n : ℕ} (P Q : WitnessedPair n)
    (a : CompactDomainDiffeomorph P.ambientDomain.domain Q.ambientDomain.domain)
    (g : CompactDomainDiffeomorph P.ribbonDomain.domain Q.ribbonDomain.domain)
    (ha : ∀ x ∈ P.ambientDomain.domain.carrier,
      P.ambientDomain.domain.extension.pullback Q.ambientDomain.domain.extension a.map
        Q.ambientDomain.liouville.primitive x = P.ambientDomain.liouville.primitive x)
    (c : ℝ) (hc : 0 < c)
    (hg : ∀ x ∈ P.ribbonDomain.domain.carrier,
      P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension g.map
        Q.ribbonDomain.liouville.primitive x = c • P.ribbonDomain.liouville.primitive x)
    (hsquare : ∀ x ∈ P.ribbonDomain.domain.carrier,
      a.map (P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x)) =
        Q.ambientDomain.domain.boundaryInclusion.map (Q.ribbonEmbedding.map (g.map x))) :
    ∃ I : CompletionIdentification P Q,
      I.ribbonEquiv = g ∧ I.scale = c ∧ I.shift = (fun _ => 0) ∧
      (∀ x ∈ P.ambientDomain.domain.carrier,
        I.ambientEquiv (P.ambientCompletion.inclusion.map x) =
          Q.ambientCompletion.inclusion.map (a.map x)) := by
  obtain ⟨f, b, hp, hn, hb, he⟩ :=
    P.ambientCompletion.exists_strictEquiv_of_compactDiffeomorph Q.ambientCompletion a ha
  have hr (x : P.ribbonDomain.domain.extension.Point) (hx : x ∈ P.ribbonDomain.domain.carrier) :
      b (P.ribbonEmbedding.map x) = Q.ribbonEmbedding.map (g.map x) := by
    apply Q.ambientDomain.domain.boundaryInclusion.embedding.injective
    exact (hb (P.ribbonEmbedding.map x)).symm.trans (hsquare x hx)
  obtain ⟨I, hf, hI, hIc⟩ := exists_of_ribbon_trajectory_square P Q f hp g c hc hg (by
    intro x hx
    exact ⟨0, by rw [he _ 0 le_rfl, hr x hx]⟩)
  refine ⟨I, hI, hIc, ?_, ?_⟩
  · funext x
    obtain ⟨r₀, hr₀⟩ := I.induced_at_infinity x
    let r := max r₀ 0
    have hleft := hr₀ r (le_max_left _ _)
    rw [hf, he x r (le_max_right _ _)] at hleft
    have hs := congrArg Prod.snd (Q.ambientCompletion.endMap_injective hleft)
    change r = r + I.shift x at hs
    linarith
  · simpa only [hf] using hn

end FsFltz.Geometry.CompletionIdentification

namespace FsFltz.Geometry
open SmoothManifold

/-- Independent collar choices of the same nonempty native compact pair
are related by an actual strict identification. The compact ambient and
ribbon maps preserve their original points, with scale one and shift zero.
No collar-width agreement is required, including for dimension-zero ribbons. -/
theorem localizedWitnessedPair_exists_completionIdentification {n : ℕ}
    (E : LiouvilleDomain (2 * n)) (F : LiouvilleDomain (2 * n - 2))
    (Λ : LiouvilleStructure E.domain) (Μ : LiouvilleStructure F.domain)
    (hΛ : Λ.primitive = E.liouville.primitive) (hΜ : Μ.primitive = F.liouville.primitive)
    (hE : E.domain.carrier.Nonempty) (hF : F.domain.carrier.Nonempty)
    (j : F.domain.extension.SmoothEmbedding E.domain.boundary)
    (b : E.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (hr : ∀ x ∈ F.domain.carrier,
      F.domain.extension.pullback E.domain.boundary j.map
        (fun y => b y • E.domain.boundaryForm E.liouville.primitive y) x =
          F.liouville.primitive x)
    (A : LiouvilleDomain.FlowCollar E)
    (A' : LiouvilleDomain.FlowCollar (⟨E.domain, Λ⟩ : LiouvilleDomain (2 * n)))
    (B : LiouvilleDomain.FlowCollar F)
    (B' : LiouvilleDomain.FlowCollar (⟨F.domain, Μ⟩ : LiouvilleDomain (2 * n - 2))) :
    let P := localizedWitnessedPair E F A B j b hb hpos hr
    let hr' : ∀ x ∈ F.domain.carrier,
        F.domain.extension.pullback E.domain.boundary j.map
          (fun y => b y • E.domain.boundaryForm Λ.primitive y) x = Μ.primitive x :=
      by simpa only [hΛ, hΜ] using hr
    let Q := localizedWitnessedPair ⟨E.domain, Λ⟩ ⟨F.domain, Μ⟩ A' B' j b hb hpos hr'
    ∃ I : CompletionIdentification P Q,
      I.scale = 1 ∧ I.shift = (fun _ => 0) ∧
      (∀ x ∈ P.ribbonDomain.domain.carrier,
        B'.originalInclusion.map (I.ribbonEquiv.map x) = B.originalInclusion.map x) ∧
      (∀ x ∈ P.ambientDomain.domain.carrier,
        ∃ y ∈ Q.ambientDomain.domain.carrier,
          A'.originalInclusion.map y = A.originalInclusion.map x ∧
          I.ambientEquiv (P.ambientCompletion.inclusion.map x) =
            Q.ambientCompletion.inclusion.map y) := by
  let P := localizedWitnessedPair E F A B j b hb hpos hr
  let hr' : ∀ x ∈ F.domain.carrier,
      F.domain.extension.pullback E.domain.boundary j.map
        (fun y => b y • E.domain.boundaryForm Λ.primitive y) x = Μ.primitive x :=
    by simpa only [hΛ, hΜ] using hr
  let Q := localizedWitnessedPair ⟨E.domain, Λ⟩ ⟨F.domain, Μ⟩ A' B' j b hb hpos hr'
  have hEa : A.localizedDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hE
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp A.image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  have hFb : B.localizedDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hF
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp B.image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  obtain ⟨a, ha, _⟩ := CompactDomain.exists_compactDiffeomorph_of_commonEmbedding
    A.localizedDomain.domain A'.localizedDomain.domain E.domain.extension hEa
    A.originalInclusion A'.originalInclusion
    (A.image_originalInclusion_carrier.trans A'.image_originalInclusion_carrier.symm)
  obtain ⟨g, hg, _⟩ := CompactDomain.exists_compactDiffeomorph_of_commonEmbedding
    B.localizedDomain.domain B'.localizedDomain.domain F.domain.extension hFb
    B.originalInclusion B'.originalInclusion
    (B.image_originalInclusion_carrier.trans B'.image_originalInclusion_carrier.symm)
  have hpa (x) (hx : x ∈ P.ambientDomain.domain.carrier) :
      P.ambientDomain.domain.extension.pullback Q.ambientDomain.domain.extension a.map
        Q.ambientDomain.liouville.primitive x = P.ambientDomain.liouville.primitive x := by
    change A.localizedDomain.domain.extension.pullback A'.localizedDomain.domain.extension a.map
      A'.localizedDomain.liouville.primitive x = A.localizedDomain.liouville.primitive x
    rw [A'.localized_primitive_pullback, A.localized_primitive_pullback, hΛ]
    exact a.pullback_of_commonEmbedding E.domain.extension A.originalInclusion
      A'.originalInclusion ha E.liouville.primitive x hx
  have hpg (x) (hx : x ∈ P.ribbonDomain.domain.carrier) :
      P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension g.map
        Q.ribbonDomain.liouville.primitive x = (1 : ℝ) • P.ribbonDomain.liouville.primitive x := by
    change B.localizedDomain.domain.extension.pullback B'.localizedDomain.domain.extension g.map
      B'.localizedDomain.liouville.primitive x = (1 : ℝ) • B.localizedDomain.liouville.primitive x
    rw [one_smul, B'.localized_primitive_pullback, B.localized_primitive_pullback, hΜ]
    exact g.pullback_of_commonEmbedding F.domain.extension B.originalInclusion
      B'.originalInclusion hg F.liouville.primitive x hx
  have hsquare (x) (hx : x ∈ P.ribbonDomain.domain.carrier) :
      a.map (P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x)) =
        Q.ambientDomain.domain.boundaryInclusion.map (Q.ribbonEmbedding.map (g.map x)) := by
    apply A'.originalInclusion.embedding.injective
    have hp : P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x) ∈
        P.ambientDomain.domain.carrier :=
      P.ambientDomain.domain.boundaryInclusion_mem_carrier _
    rw [ha _ (a.contains_source hp)]
    change E.domain.boundaryInclusion.map (j.map (B.originalInclusion.map x)) =
      E.domain.boundaryInclusion.map (j.map (B'.originalInclusion.map (g.map x)))
    rw [hg x (g.contains_source hx)]
  obtain ⟨I, hIg, hIc, hIs, hIa⟩ := CompletionIdentification.exists_of_compactPairSquare
    P Q a g hpa 1 zero_lt_one hpg hsquare
  refine ⟨I, hIc, hIs, ?_, ?_⟩
  · intro x hx
    rw [hIg]
    exact hg x (g.contains_source hx)
  · intro x hx
    exact ⟨a.map x, a.maps_source hx, ha x (a.contains_source hx), hIa x hx⟩

end FsFltz.Geometry

namespace FsFltz
open Geometry SmoothManifold

/-- Actual scalar normalization supplies the primitive equation needed for
a strict comparison between independently chosen zero-endpoint collars.
Both endpoint structures live on the same already constructed native
compact domain; no completed comparison is assumed. -/
theorem tailoringFamily_zero_localized_pair_identification {n : ℕ}
    (I : ToricInput n) (β K : ℝ) (α : (lgManifold n).Form 1)
    (D : CompactDomain (2 * n)) (Λnorm Λhol : LiouvilleStructure D)
    (F : LiouvilleDomain (2 * n - 2))
    (hD : D.carrier.Nonempty) (hF : F.domain.carrier.Nonempty)
    (J : D.extension.SmoothEmbedding (lgManifold n))
    (hnorm : Λnorm.primitive = D.extension.pullback (lgManifold n) J.map
      ((lgManifold n).rankTwoPrimitive α (tailoringFamily I β 0) K))
    (hhol : Λhol.primitive = D.extension.pullback (lgManifold n) J.map
      ((lgManifold n).rankTwoPrimitive α (W (I.alongCoefficientPath 1))
        (K / Real.exp β ^ 2)))
    (j : F.domain.extension.SmoothEmbedding D.boundary)
    (hr : ∀ x ∈ F.domain.carrier,
      F.domain.extension.pullback D.boundary j.map
        (fun y => (1 : ℝ) • D.boundaryForm Λnorm.primitive y) x = F.liouville.primitive x)
    (A : LiouvilleDomain.FlowCollar (⟨D, Λnorm⟩ : LiouvilleDomain (2 * n)))
    (A' : LiouvilleDomain.FlowCollar (⟨D, Λhol⟩ : LiouvilleDomain (2 * n)))
    (B B' : LiouvilleDomain.FlowCollar F) :
    let hr' : ∀ x ∈ F.domain.carrier,
        F.domain.extension.pullback D.boundary j.map
          (fun y => (1 : ℝ) • D.boundaryForm Λhol.primitive y) x = F.liouville.primitive x := by
      have he : Λhol.primitive = Λnorm.primitive := by
        rw [hhol, hnorm, tailoringFamily_zero_rankTwoPrimitive]
      simpa only [he] using hr
    let P := localizedWitnessedPair ⟨D, Λnorm⟩ F A B j (fun _ => 1)
      contMDiff_const (fun _ => zero_lt_one) hr
    let Q := localizedWitnessedPair ⟨D, Λhol⟩ F A' B' j (fun _ => 1)
      contMDiff_const (fun _ => zero_lt_one) hr'
    ∃ q : CompletionIdentification P Q,
      q.scale = 1 ∧ q.shift = (fun _ => 0) ∧
      (∀ x ∈ P.ribbonDomain.domain.carrier,
        B'.originalInclusion.map (q.ribbonEquiv.map x) = B.originalInclusion.map x) ∧
      (∀ x ∈ P.ambientDomain.domain.carrier,
        ∃ y ∈ Q.ambientDomain.domain.carrier,
          A'.originalInclusion.map y = A.originalInclusion.map x ∧
          q.ambientEquiv (P.ambientCompletion.inclusion.map x) =
            Q.ambientCompletion.inclusion.map y) := by
  have he : Λhol.primitive = Λnorm.primitive := by
    rw [hhol, hnorm, tailoringFamily_zero_rankTwoPrimitive]
  exact localizedWitnessedPair_exists_completionIdentification ⟨D, Λnorm⟩ F
    Λhol F.liouville he rfl hD hF j (fun _ => 1) contMDiff_const
    (fun _ => zero_lt_one) hr A A' B B'

end FsFltz
