import FsFltz.Geometry.PotentialPathRoundedAmbientFamily
import FsFltz.Geometry.PotentialPathRoundedPairCarrier
import FsFltz.Geometry.PotentialPathEmbeddedRibbonLiouville
import FsFltz.Geometry.TailoringRoundedPairFamily

/-!
# The actual completed holomorphic pair deformation

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1049,
and assembly, lines 2148–2158. One constructed simultaneous transport
supplies the fixed carriers, all native Liouville structures, and witness
one. Its actual localized presentations and completions are retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set
namespace FsFltz
open Geometry
variable {n : ℕ}

/-- The actual holomorphic coefficient/potential path produces a smooth deformation of
completed witnessed pairs, with witnessing factor one. The explicit pair
formula and all localized whole/frontier images retain the same flow-built
carriers and the same restricted boundary embedding. -/
theorem coefficientPath_potentialPath_exists_uniform_rounded_pairDeformation_with_presentations
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
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
      ∃ Kstar : ℝ, 0 < Kstar ∧
      coefficientPotentialPathThreshold I (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) hc hlower (Real.exp β) ≤ Kstar ∧
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ (E : CompactDomain (2 * n)) (D : CompactDomain (2 * n - 2))
        (k : D.extension.SmoothEmbedding E.boundary)
        (J : Parameter → E.extension.SmoothEmbedding (lgManifold n))
        (Λ : (K : ℝ) → Kstar ≤ K → Parameter → LiouvilleStructure E)
        (Μ : Parameter → LiouvilleStructure D),
        let jR := fun t => (J t).comp (E.boundaryInclusion.comp k)
        E.carrier.Nonempty ∧ D.carrier.Nonempty ∧
        E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (jR t).map) ∧
        (∀ t : Parameter,
          (J t).map '' E.carrier = {y | potentialPath_roundedDefiningFunction I φ (Real.exp β)
            (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) ≤ 0} ∧
          (J t).map '' frontier E.carrier =
            {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) = 0} ∧
          (jR t).map '' D.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
          (jR t).map '' frontier D.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus}) ∧
        (∀ K hK t, (Λ K hK t).primitive = E.extension.pullback (lgManifold n) (J t).map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)) (W (I.alongCoefficientPath t.val)) K)) ∧
        (∀ t, (Μ t).primitive = D.extension.pullback (lgManifold n) (jR t).map
          (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))) ∧
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
                {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) ≤ 0} ∧
              ((J t).comp (A t).originalInclusion).map '' frontier (A t).localizedDomain.domain.carrier =
                {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) = 0} ∧
              ((jR t).comp (B t).originalInclusion).map '' (B t).localizedDomain.domain.carrier =
                {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
              ((jR t).comp (B t).originalInclusion).map '' frontier (B t).localizedDomain.domain.carrier =
                {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus} := by
  classical
  obtain ⟨Fc, hFc, hcarriers⟩ :=
    Geometry.ToricInput.coefficientPath_potentialPath_exists_uniform_rounded_fixedPair_carriers
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fr, hFr, Br, hBr, hribbonFamily⟩ :=
    Geometry.ToricInput.coefficientPath_potentialPath_exists_uniform_embeddedRibbon_liouvilleFamily
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨A₀, R₀, hA₀, hR₀, hambient⟩ :=
    Geometry.ToricInput.coefficientPath_potentialPath_rounded_embedded_liouvilleFamily
      I hφ hc hlower hupper hEnd hhom hL hend
  let F := max Fc (max Fr 1)
  have hF : 0 < F := hFc.trans_le (le_max_left _ _)
  refine ⟨F, hF, ?_⟩
  intro Cplus hCF
  obtain ⟨Bc, hBc, hcarriers⟩ := hcarriers Cplus ((le_max_left _ _).trans_lt hCF)
  let β₀ := max Bc (max Br (max R₀ (4 * A₀ + 1)))
  refine ⟨β₀, hBc.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβc : Bc ≤ β := (le_max_left _ _).trans hβ
  have hβr : Br ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβR : R₀ ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβA : 4 * A₀ + 1 ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hR : R₀ ≤ Real.exp β := by linarith [Real.add_one_le_exp β]
  have hCone : 1 ≤ Cplus :=
    ((le_max_right Fr 1).trans (le_max_right Fc (max Fr 1))).trans hCF.le
  have hA : 2 * A₀ ≤ Cplus ^ 2 * β ^ 2 / 2 := by
    have hβone : 1 ≤ β := by linarith
    have hβsq : β ≤ β ^ 2 := by nlinarith
    have hCsq : 1 ≤ Cplus ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hCsq (sq_nonneg β)]
  obtain ⟨Kstar, hKstar, hKpath, hambient⟩ := hambient (Real.exp β) hR
  refine ⟨Kstar, hKstar, hKpath, ?_⟩
  intro Aminus hlo hhi
  have hFcA : Fc ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlo
    gcongr
    exact le_max_left Fc (max Fr 1)
  have hFrA : Fr ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlo
    gcongr
    exact (le_max_left Fr 1).trans (le_max_right Fc (max Fr 1))
  obtain ⟨δc, hδc, hgapc, hcarriers⟩ := hcarriers β hβc Aminus hFcA hhi
  obtain ⟨δa, hδa, hgapa, hambient⟩ :=
    hambient (Cplus ^ 2 * β ^ 2 / 2) hA Aminus hhi
  refine ⟨min δc δa, lt_min hδc hδa, (min_le_left _ _).trans_lt hgapc, ?_⟩
  intro m hm hmd
  obtain ⟨E, D₀, χ, i, k₀, Φ, J, hEne, hDne, _hrange, hk₀, _hχ, _hχfront,
    _hJzero, _hJflow, hJ, hW₀, himages⟩ :=
      hcarriers m hm (hmd.trans (min_le_left _ _))
  have hambientFamily (K : ℝ) (hK : Kstar ≤ K) :=
    hambient m hm (hmd.trans (min_le_right _ _)) E J hJ
      (fun t => (himages t).1) (fun t => (himages t).2.1) K hK
  choose Λ hΛ hΛforms hΛfields hΛsymp hΛcompletion using hambientFamily
  obtain ⟨O, hDO, Μ, hW', hDimages, _hkernel, hΜ, _hfield, hΜforms, _hΜfields,
    _hΜsymp, _hΜcompletion, hcompat⟩ := hribbonFamily β hβr Aminus hFrA D₀
      (fun t => (J t).comp i) hW₀
      (fun t => ⟨(himages t).2.2.1, (himages t).2.2.2⟩)
  let D := D₀.restrict O hDO
  let k : D.extension.SmoothEmbedding E.boundary :=
    k₀.comp (D₀.extension.restrictInclusion O)
  let jR := fun t => (J t).comp (E.boundaryInclusion.comp k)
  have hWeq (t : Parameter) : (jR t).map =
      (tailoringRibbonRestrictedEmbedding D₀ ((J t).comp i) O hDO).map := by
    apply ContMDiffMap.ext
    intro x
    change (J t).map (E.boundaryInclusion.map (k₀.map x.val)) = (J t).map (i.map x.val)
    rw [hk₀]
  have hWs : D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (jR t).map) := by
    simpa only [hWeq] using hW'
  have hDne' : D.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hDne
    exact ⟨⟨x, hDO hx⟩, hx⟩
  have hΜ' (t : Parameter) : (Μ t).primitive =
      D.extension.pullback (lgManifold n) (jR t).map (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)) := by
    rw [hWeq]
    exact hΜ t
  have himages' (t : Parameter) :
      (J t).map '' E.carrier = {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) ≤ 0} ∧
      (J t).map '' frontier E.carrier =
        {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) = 0} ∧
      (jR t).map '' D.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
      (jR t).map '' frontier D.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus} := by
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
    change D.extension.pullback (lgManifold n) (jR t).map _ x = _
    rw [hWeq]
    exact hcompat t K x hx
  have hks : D.extension.IsSmoothIntervalMapFamily E.boundary (fun _ => k.map) := by
    refine ⟨fun _ => k.map, ⟨univ, isOpen_univ, subset_univ _, ?_⟩, fun _ => rfl⟩
    exact (k.map.contMDiff.comp contMDiff_snd).contMDiffOn
  have hbs : E.boundary.IsSmoothIntervalScalarFamily (fun _ _ => (1 : ℝ)) := by
    refine ⟨fun _ _ => 1, ?_, fun _ => rfl⟩
    intro a
    exact ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  let ambient := E.localizedCompletionFamily (Λ K hK) (hΛforms K hK)
  let ribbon := D.localizedCompletionFamily Μ hΜforms
  let A := ambient.collars
  let B := ribbon.collars
  let Q := E.localizedPairDeformation D (Λ K hK) Μ (fun _ => k) (fun _ _ => 1)
    (hΛforms K hK) hΜforms hks hbs (fun _ _ => zero_lt_one) ambient ribbon hribbon
  refine ⟨hribbon, (hΛforms K hK), hΜforms, hks, hbs,
    ambient, ribbon, Q, rfl, rfl, ?_⟩
  intro t
  have ha := (A t).image_originalInclusion_carrier
  have haf := (A t).image_originalInclusion_frontier
  have hb := (B t).image_originalInclusion_carrier
  have hbf := (B t).image_originalInclusion_frontier
  change ((J t).map ∘ (A t).originalInclusion.map) '' _ = _ ∧
    ((J t).map ∘ (A t).originalInclusion.map) '' _ = _ ∧
    ((jR t).map ∘ (B t).originalInclusion.map) '' _ = _ ∧
    ((jR t).map ∘ (B t).originalInclusion.map) '' _ = _
  rw [Set.image_comp, Set.image_comp, Set.image_comp, Set.image_comp]
  rw [ha, haf, hb, hbf]
  exact himages' t


end FsFltz
