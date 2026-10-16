import FsFltz.Geometry.TailoringRoundedAmbientFamily
import FsFltz.Geometry.TailoringEmbeddedRibbonLiouville
import FsFltz.Geometry.PairFamilyConstruction
import FsFltz.Geometry.TailoringRoundedCompletionMarking

/-!
# Actual completed pair deformations for rounded tailoring

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and the marked deformation, lines 1239–1326; `geoemtric-part-fsf.tex`,
`def:pair`, lines 119–160, and `def:chain`, lines 163–200.
The same ambient carrier and its same-flow embedded full ribbon support
actual Liouville structures, witnessing factor one, and constructed smooth
localized completed pair families. Named whole-fiber completion markings
and normalized endpoint identifications remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.CompactDomain
open SmoothManifold

/-- Restriction to the actual native boundary and then to its embedded
ribbon is exactly the pullback along the composed ambient embedding. -/
theorem pullback_boundaryForm_of_ambient_pullback {a d e : ℕ}
    (E : CompactDomain a) (D : SmoothManifold d) (M : SmoothManifold e)
    (k : D.SmoothEmbedding E.boundary) (J : E.extension.SmoothEmbedding M)
    (α : M.Form 1) :
    D.pullback E.boundary k.map (E.boundaryForm (E.extension.pullback M J.map α)) =
      D.pullback M (J.comp (E.boundaryInclusion.comp k)).map α := by
  unfold boundaryForm
  rw [← D.pullback_comp E.boundary E.extension
    (k.map.contMDiff.mdifferentiable (by simp))
    (E.boundaryInclusion.map.contMDiff.mdifferentiable (by simp))]
  change D.pullback E.extension (E.boundaryInclusion.comp k).map
    (E.extension.pullback M J.map α) = _
  rw [← D.pullback_comp E.extension M
    ((E.boundaryInclusion.comp k).map.contMDiff.mdifferentiable (by simp))
    (J.map.contMDiff.mdifferentiable (by simp))]
  rfl

end FsFltz.Geometry.CompactDomain

namespace FsFltz.Geometry.LiouvilleDomain.FlowCollar

/-- The collar localization retains the entire native frontier under its
actual original inclusion, including a possibly empty frontier. -/
theorem image_originalInclusion_frontier {d : ℕ} {D : LiouvilleDomain d}
    (C : LiouvilleDomain.FlowCollar D) :
    C.originalInclusion.map '' frontier C.localizedDomain.domain.carrier =
      frontier D.domain.carrier := by
  rw [← C.localizedDomain.domain.boundary_range, ← D.domain.boundary_range]
  ext x
  constructor
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨C.localizedDomain.domain.boundaryInclusion.map b, ⟨b, rfl⟩, rfl⟩

end FsFltz.Geometry.LiouvilleDomain.FlowCollar

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- Actual finite-input rounded tailoring produces a smooth deformation of
completed witnessed pairs, with witnessing factor one. The explicit pair
formula and all localized whole/frontier images retain the same flow-built
carriers and the same restricted boundary embedding. -/
theorem tailoringFamily_exists_uniform_rounded_pairDeformation_with_presentations
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∀ Cplus : ℝ, F < Cplus →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ (E : CompactDomain (2 * n)) (D : CompactDomain (2 * n - 2))
        (k : D.extension.SmoothEmbedding E.boundary)
        (J : Parameter → E.extension.SmoothEmbedding (lgManifold n))
        (Λ : (K : ℝ) → Kstar ≤ K → Parameter → LiouvilleStructure E)
        (Μ : Parameter → LiouvilleStructure D),
        let W := fun t => (J t).comp (E.boundaryInclusion.comp k)
        E.carrier.Nonempty ∧ D.carrier.Nonempty ∧
        E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (W t).map) ∧
        (∀ t : Parameter,
          (J t).map '' E.carrier = tailoringRoundedDomain I φ β t.val R
            (Cplus ^ 2 * β ^ 2 / 2) m ∧
          (J t).map '' frontier E.carrier =
            {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
          (W t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
          (W t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus}) ∧
        (∀ K hK t, (Λ K hK t).primitive = E.extension.pullback (lgManifold n) (J t).map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K)) ∧
        (∀ t, (Μ t).primitive = D.extension.pullback (lgManifold n) (W t).map
          (lambdaPotentialForm φ)) ∧
        ∀ K hK,
          ∃ hribbon : ∀ t x, x ∈ D.carrier →
            D.extension.pullback E.boundary k.map
              (fun y => (1 : ℝ) • E.boundaryForm (Λ K hK t).primitive y) x = (Μ t).primitive x,
          ∃ (hα : E.extension.IsSmoothIntervalFormFamily (fun t => (Λ K hK t).primitive))
            (hμ : D.extension.IsSmoothIntervalFormFamily (fun t => (Μ t).primitive))
            (hk : D.extension.IsSmoothIntervalMapFamily E.boundary (fun _ => k.map))
            (hb : E.boundary.IsSmoothIntervalScalarFamily (fun _ _ => (1 : ℝ)))
            (ambient : LocalizedCompletionFamily E (Λ K hK))
            (ribbon : LocalizedCompletionFamily D Μ),
          let A := ambient.collars
          let B := ribbon.collars
          ∃ Q : PairDeformation n,
            Q = E.localizedPairDeformation D (Λ K hK) Μ (fun _ => k) (fun _ _ => 1)
              hα hμ hk hb (fun _ _ => zero_lt_one) ambient ribbon hribbon ∧
            Q.pair = (fun t => localizedWitnessedPair ⟨E, Λ K hK t⟩ ⟨D, Μ t⟩ (A t) (B t)
              k (fun _ => 1) contMDiff_const (fun _ => zero_lt_one) (hribbon t)) ∧
            ∀ t : Parameter,
              ((J t).comp (A t).originalInclusion).map '' (A t).localizedDomain.domain.carrier =
                tailoringRoundedDomain I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m ∧
              ((J t).comp (A t).originalInclusion).map '' frontier (A t).localizedDomain.domain.carrier =
                {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
              ((W t).comp (B t).originalInclusion).map '' (B t).localizedDomain.domain.carrier =
                {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
              ((W t).comp (B t).originalInclusion).map '' frontier (B t).localizedDomain.domain.carrier =
                {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus} := by
  classical
  obtain ⟨Fa, hFa, hambient⟩ := tailoringFamily_exists_uniform_rounded_ambient_liouvilleFamily
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fr, hFr, Br, hBr, hribbonFamily⟩ :=
    tailoringFamily_exists_uniform_embeddedRibbon_liouvilleFamily
      I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  let F := max Fa Fr
  have hF : 0 < F := hFa.trans_le (le_max_left _ _)
  refine ⟨F, hF, ?_⟩
  intro Cplus hCF
  obtain ⟨Ba, hBa, hambient⟩ := hambient Cplus ((le_max_left _ _).trans_lt hCF)
  refine ⟨max Ba Br, hBa.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβa := (le_max_left Ba Br).trans hβ
  have hβr := (le_max_right Ba Br).trans hβ
  obtain ⟨Kstar, hKstar, hambient⟩ := hambient β hβa
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hlo hhi
  have hFaA : Fa ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlo
    gcongr
    exact le_max_left Fa Fr
  have hFrA : Fr ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlo
    gcongr
    exact le_max_right Fa Fr
  obtain ⟨δ, hδ, hgap, hambient⟩ := hambient R hR Aminus hFaA hhi
  refine ⟨δ, hδ, hgap, ?_⟩
  intro m hm hmd
  obtain ⟨E, D₀, χ, i, k₀, Φ, J, Λ, hEne, hDne, _hrange, hk₀, _hχ, _hχfront,
    _hJzero, _hJflow, hJ, hW₀, himages, hΛ, hambientSmooth⟩ := hambient m hm hmd
  obtain ⟨O, hDO, Μ, hW', hDimages, _hkernel, hΜ, _hfield, hΜforms, _hΜfields,
    _hΜsymp, _hΜcompletion, hcompat⟩ := hribbonFamily β hβr Aminus hFrA D₀
      (fun t => (J t).comp i) hW₀
      (fun t => ⟨(himages t).2.2.1, (himages t).2.2.2⟩)
  let D := D₀.restrict O hDO
  let k : D.extension.SmoothEmbedding E.boundary :=
    k₀.comp (D₀.extension.restrictInclusion O)
  let W := fun t => (J t).comp (E.boundaryInclusion.comp k)
  have hWeq (t : Parameter) : (W t).map =
      (tailoringRibbonRestrictedEmbedding D₀ ((J t).comp i) O hDO).map := by
    apply ContMDiffMap.ext
    intro x
    change (J t).map (E.boundaryInclusion.map (k₀.map x.val)) = (J t).map (i.map x.val)
    rw [hk₀]
  have hWs : D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (W t).map) := by
    simpa only [hWeq] using hW'
  have hDne' : D.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hDne
    exact ⟨⟨x, hDO hx⟩, hx⟩
  have hΜ' (t : Parameter) : (Μ t).primitive =
      D.extension.pullback (lgManifold n) (W t).map (lambdaPotentialForm φ) := by
    rw [hWeq]
    exact hΜ t
  have himages' (t : Parameter) :
      (J t).map '' E.carrier = tailoringRoundedDomain I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m ∧
      (J t).map '' frontier E.carrier =
        {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
      (W t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
      (W t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus} := by
    refine ⟨(himages t).1, (himages t).2.1, ?_⟩
    rw [hWeq]
    exact hDimages t
  refine ⟨E, D, k, J, Λ, Μ, hEne, hDne', hJ, hWs, himages', hΛ, hΜ', ?_⟩
  intro K hK
  have hribbon : ∀ t x, x ∈ D.carrier →
      D.extension.pullback E.boundary k.map
        (fun y => (1 : ℝ) • E.boundaryForm (Λ K hK t).primitive y) x = (Μ t).primitive x := by
    intro t x hx
    simp only [one_smul]
    rw [hΛ, E.pullback_boundaryForm_of_ambient_pullback]
    change D.extension.pullback (lgManifold n) (W t).map _ x = _
    rw [hWeq]
    exact hcompat t K x hx
  have hks : D.extension.IsSmoothIntervalMapFamily E.boundary (fun _ => k.map) := by
    refine ⟨fun _ => k.map, ⟨univ, isOpen_univ, subset_univ _, ?_⟩, fun _ => rfl⟩
    exact (k.map.contMDiff.comp contMDiff_snd).contMDiffOn
  have hbs : E.boundary.IsSmoothIntervalScalarFamily (fun _ _ => (1 : ℝ)) := by
    refine ⟨fun _ _ => 1, ?_, fun _ => rfl⟩
    intro a
    exact ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  let ambient := E.localizedCompletionFamily (Λ K hK) (hambientSmooth K hK).1
  let ribbon := D.localizedCompletionFamily Μ hΜforms
  let A := ambient.collars
  let B := ribbon.collars
  let Q := E.localizedPairDeformation D (Λ K hK) Μ (fun _ => k) (fun _ _ => 1)
    (hambientSmooth K hK).1 hΜforms hks hbs (fun _ _ => zero_lt_one) ambient ribbon hribbon
  refine ⟨hribbon, (hambientSmooth K hK).1, hΜforms, hks, hbs,
    ambient, ribbon, Q, rfl, rfl, ?_⟩
  intro t
  have ha := (A t).image_originalInclusion_carrier
  have haf := (A t).image_originalInclusion_frontier
  have hb := (B t).image_originalInclusion_carrier
  have hbf := (B t).image_originalInclusion_frontier
  change ((J t).map ∘ (A t).originalInclusion.map) '' _ = _ ∧
    ((J t).map ∘ (A t).originalInclusion.map) '' _ = _ ∧
    ((W t).map ∘ (B t).originalInclusion.map) '' _ = _ ∧
    ((W t).map ∘ (B t).originalInclusion.map) '' _ = _
  rw [Set.image_comp, Set.image_comp, Set.image_comp, Set.image_comp]
  rw [ha, haf, hb, hbf]
  exact himages' t

/-- The original pair-deformation interface, retaining every full carrier and frontier image. -/
theorem tailoringFamily_exists_uniform_rounded_pairDeformation
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∀ Cplus : ℝ, F < Cplus →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ (E : CompactDomain (2 * n)) (D : CompactDomain (2 * n - 2))
        (k : D.extension.SmoothEmbedding E.boundary)
        (J : Parameter → E.extension.SmoothEmbedding (lgManifold n))
        (Λ : (K : ℝ) → Kstar ≤ K → Parameter → LiouvilleStructure E)
        (Μ : Parameter → LiouvilleStructure D),
        let W := fun t => (J t).comp (E.boundaryInclusion.comp k)
        E.carrier.Nonempty ∧ D.carrier.Nonempty ∧
        E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (W t).map) ∧
        (∀ t : Parameter,
          (J t).map '' E.carrier = tailoringRoundedDomain I φ β t.val R
            (Cplus ^ 2 * β ^ 2 / 2) m ∧
          (J t).map '' frontier E.carrier =
            {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
          (W t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
          (W t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus}) ∧
        (∀ K hK t, (Λ K hK t).primitive = E.extension.pullback (lgManifold n) (J t).map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K)) ∧
        (∀ t, (Μ t).primitive = D.extension.pullback (lgManifold n) (W t).map
          (lambdaPotentialForm φ)) ∧
        ∀ K hK,
          ∃ hribbon : ∀ t x, x ∈ D.carrier →
            D.extension.pullback E.boundary k.map
              (fun y => (1 : ℝ) • E.boundaryForm (Λ K hK t).primitive y) x = (Μ t).primitive x,
          ∃ A : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨E, Λ K hK t⟩ : LiouvilleDomain (2 * n)),
          ∃ B : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨D, Μ t⟩ : LiouvilleDomain (2 * n - 2)),
          ∃ Q : PairDeformation n,
            Q.pair = (fun t => localizedWitnessedPair ⟨E, Λ K hK t⟩ ⟨D, Μ t⟩ (A t) (B t)
              k (fun _ => 1) contMDiff_const (fun _ => zero_lt_one) (hribbon t)) ∧
            ∀ t : Parameter,
              ((J t).comp (A t).originalInclusion).map '' (A t).localizedDomain.domain.carrier =
                tailoringRoundedDomain I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m ∧
              ((J t).comp (A t).originalInclusion).map '' frontier (A t).localizedDomain.domain.carrier =
                {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
              ((W t).comp (B t).originalInclusion).map '' (B t).localizedDomain.domain.carrier =
                {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
              ((W t).comp (B t).originalInclusion).map '' frontier (B t).localizedDomain.domain.carrier =
                {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus} := by
  obtain ⟨F, hF, hfamily⟩ := tailoringFamily_exists_uniform_rounded_pairDeformation_with_presentations
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, ?_⟩
  intro Cplus hC
  obtain ⟨β₀, hβ₀, hfamily⟩ := hfamily Cplus hC
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨Kstar, hKstar, hfamily⟩ := hfamily β hβ
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hlo hhi
  obtain ⟨δ, hδ, hgap, hfamily⟩ := hfamily R hR Aminus hlo hhi
  refine ⟨δ, hδ, hgap, ?_⟩
  intro m hm hmd
  obtain ⟨E, D, k, J, Λ, Μ, hE, hD, hJ, hW, himages, hΛ, hΜ, hfamily⟩ := hfamily m hm hmd
  refine ⟨E, D, k, J, Λ, Μ, hE, hD, hJ, hW, himages, hΛ, hΜ, ?_⟩
  intro K hK
  obtain ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, _hQ, hpairs, himages⟩ := hfamily K hK
  exact ⟨hribbon, ambient.collars, ribbon.collars, Q, hpairs, himages⟩

end FsFltz
