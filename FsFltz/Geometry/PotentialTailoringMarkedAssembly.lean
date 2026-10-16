import FsFltz.Geometry.PotentialTailoringMarkedChain
import FsFltz.Geometry.PotentialPathRoundedMarkingFamily

/-!
# Finite-input construction of the actual marked comparison prefix

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1049,
`eq:normalizedrounding` and common markings, lines 1260–1314, and assembly,
lines 2127–2258. Both marked families are constructed once and retained;
the strict junction is constructed directly on their chosen completions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- Finite geometric data construct the actual three-step marked prefix,
with the original pointwise markings and smooth completed maps retained. -/
theorem coefficientPath_tailoring_exists_uniform_marked_prefix
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
      ∃ Kstar : ℝ, 0 < Kstar ∧
      coefficientPotentialPathThreshold I (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
        hc hlower (Real.exp β) ≤ Kstar / Real.exp β ^ 2 ∧
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ → ∀ K : ℝ, Kstar ≤ K →
        Nonempty (PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m) := by
  classical
  obtain ⟨FH, hFH, hhol⟩ :=
    coefficientPath_potentialPath_exists_uniform_rounded_pairDeformation_with_smooth_markings
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨FT, hFT, htail⟩ :=
    tailoringFamily_exists_uniform_rounded_pairDeformation_with_fullFiber_ribbon_markings
      I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  let F := max FH FT
  refine ⟨F, hFH.trans_le (le_max_left _ _), ?_⟩
  intro Cplus hCplus
  obtain ⟨BH, hBH, hhol⟩ := hhol Cplus ((le_max_left _ _).trans_lt hCplus)
  obtain ⟨BT, hBT, htail⟩ := htail Cplus ((le_max_right _ _).trans_lt hCplus)
  refine ⟨max BH BT, hBH.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨KH, hKH, hthreshold, hhol⟩ := hhol β ((le_max_left _ _).trans hβ)
  obtain ⟨KT, hKT, htail⟩ := htail β ((le_max_right _ _).trans hβ)
  let Kstar := max (KH * Real.exp β ^ 2) KT
  refine ⟨Kstar, hKT.trans_le (le_max_right _ _),
    hthreshold.trans ((le_div_iff₀ (sq_pos_of_pos (Real.exp_pos β))).mpr (le_max_left _ _)), ?_⟩
  intro Aminus hlo hhi
  have hFHlevel : FH ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlo
    gcongr
    exact le_max_left FH FT
  have hFTlevel : FT ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlo
    gcongr
    exact le_max_right FH FT
  obtain ⟨δH, hδH, hgapH, hhol⟩ := hhol Aminus hFHlevel hhi
  obtain ⟨δT, hδT, _hgapT, htail⟩ := htail (Real.exp β) (Real.exp_pos β) Aminus hFTlevel hhi
  refine ⟨min δH δT, lt_min hδH hδT, (min_le_left _ _).trans_lt hgapH, ?_⟩
  intro m hm hmd K hK
  have hKH' : KH ≤ K / Real.exp β ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos β))).mpr ((le_max_left _ _).trans hK)
  have hKT' : KT ≤ K := (le_max_right _ _).trans hK
  obtain ⟨EH, DH, kH, jH, ΛH, ΜH, hEH, hDH, _hsJH, _hsRH, _himagesH,
    hΛH, hΜH, hcompleteH⟩ := hhol m hm (hmd.trans (min_le_left _ _))
  obtain ⟨ET, DT, kT, jT, ΛT, ΜT, hET, hDT, _hsJT, _hsRT, _himagesT,
    hΛT, hΜT, hcompleteT⟩ := htail m hm (hmd.trans (min_le_right _ _))
  obtain ⟨hrH, hαH, hμH, hkH, hbH, ambientH, ribbonH, H, heH, _hpH, hlocH, hK0, qH, hsmarkH, hRMH⟩ :=
    hcompleteH (K / Real.exp β ^ 2) hKH'
  obtain ⟨hrT, hαT, hμT, hkT, hbT, ambientT, ribbonT, T, heT, _hpT, hlocT, hRMT, hAMT⟩ :=
    hcompleteT K hKT'
  subst H
  subst T
  let H := EH.localizedPairDeformation DH (ΛH (K / Real.exp β ^ 2) hKH') ΜH
    (fun _ => kH) (fun _ _ => 1) hαH hμH hkH hbH (fun _ _ => zero_lt_one) ambientH ribbonH hrH
  let T := ET.localizedPairDeformation DT (ΛT K hKT') ΜT
    (fun _ => kT) (fun _ _ => 1) hαT hμT hkT hbT (fun _ _ => zero_lt_one) ambientT ribbonT hrT
  let AH := ambientH.collars
  let BH := ribbonH.collars
  let AT := ambientT.collars
  let BT := ribbonT.collars
  let JH (t : Parameter) : (H.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n) :=
    (jH t).comp (AH t).originalInclusion
  let JT (t : Parameter) : (T.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n) :=
    (jT t).comp (AT t).originalInclusion
  let RH := fun t => (JH t).comp
    ((H.pair t).ambientDomain.domain.boundaryInclusion.comp (H.pair t).ribbonEmbedding)
  let RT := fun t => (JT t).comp
    ((T.pair t).ambientDomain.domain.boundaryInclusion.comp (T.pair t).ribbonEmbedding)
  have hRHeq (t : Parameter) : (RH t).map =
      (((jH t).comp (EH.boundaryInclusion.comp kH)).comp (BH t).originalInclusion).map := rfl
  have hRTeq (t : Parameter) : (RT t).map =
      (((jT t).comp (ET.boundaryInclusion.comp kT)).comp (BT t).originalInclusion).map := rfl
  have hdataH (t : Parameter) :
      (JH t).map '' (H.pair t).ambientDomain.domain.carrier =
        {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) ≤ 0} ∧
      (JH t).map '' frontier (H.pair t).ambientDomain.domain.carrier =
        {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) = 0} ∧
      (RH t).map '' (H.pair t).ribbonDomain.domain.carrier =
        {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
      (RH t).map '' frontier (H.pair t).ribbonDomain.domain.carrier =
        {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus} ∧
      (H.pair t).ambientDomain.liouville.primitive =
        (H.pair t).ambientDomain.domain.extension.pullback (lgManifold n) (JH t).map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
            (W (I.alongCoefficientPath t.val)) (K / Real.exp β ^ 2)) ∧
      (H.pair t).ribbonDomain.liouville.primitive =
        (H.pair t).ribbonDomain.domain.extension.pullback (lgManifold n) (RH t).map
          (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)) ∧
      (H.pair t).witness = (fun _ => 1) := by
    have hloc := hlocH t
    rw [← hRHeq] at hloc
    refine ⟨hloc.1, hloc.2.1, hloc.2.2.1, hloc.2.2.2, ?_, ?_, rfl⟩
    · change (AH t).localizedDomain.liouville.primitive = _
      rw [(AH t).localized_primitive_pullback, hΛH]
      rw [← (AH t).localizedDomain.domain.extension.pullback_comp EH.extension (lgManifold n)
        ((AH t).originalInclusion.map.contMDiff.mdifferentiable (by simp))
        ((jH t).map.contMDiff.mdifferentiable (by simp))]
      rfl
    · change (BH t).localizedDomain.liouville.primitive = _
      rw [(BH t).localized_primitive_pullback, hΜH, hRHeq]
      rw [← (BH t).localizedDomain.domain.extension.pullback_comp DH.extension (lgManifold n)
        ((BH t).originalInclusion.map.contMDiff.mdifferentiable (by simp))
        (((jH t).comp (EH.boundaryInclusion.comp kH)).map.contMDiff.mdifferentiable (by simp))]
      rfl
  have hdataT (t : Parameter) :
      (JT t).map '' (T.pair t).ambientDomain.domain.carrier =
        tailoringRoundedDomain I φ β t.val (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m ∧
      (JT t).map '' frontier (T.pair t).ambientDomain.domain.carrier =
        {y | tailoringRoundedDefiningFunction I φ β t.val (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
      (RT t).map '' (T.pair t).ribbonDomain.domain.carrier =
        {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
      (RT t).map '' frontier (T.pair t).ribbonDomain.domain.carrier =
        {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus} ∧
      (T.pair t).ambientDomain.liouville.primitive =
        (T.pair t).ambientDomain.domain.extension.pullback (lgManifold n) (JT t).map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) ∧
      (T.pair t).ribbonDomain.liouville.primitive =
        (T.pair t).ribbonDomain.domain.extension.pullback (lgManifold n) (RT t).map (lambdaPotentialForm φ) ∧
      (T.pair t).witness = (fun _ => 1) := by
    have hloc := hlocT t
    rw [← hRTeq] at hloc
    refine ⟨hloc.1, hloc.2.1, hloc.2.2.1, hloc.2.2.2, ?_, ?_, rfl⟩
    · change (AT t).localizedDomain.liouville.primitive = _
      rw [(AT t).localized_primitive_pullback, hΛT]
      rw [← (AT t).localizedDomain.domain.extension.pullback_comp ET.extension (lgManifold n)
        ((AT t).originalInclusion.map.contMDiff.mdifferentiable (by simp))
        ((jT t).map.contMDiff.mdifferentiable (by simp))]
      rfl
    · change (BT t).localizedDomain.liouville.primitive = _
      rw [(BT t).localized_primitive_pullback, hΜT, hRTeq]
      rw [← (BT t).localizedDomain.domain.extension.pullback_comp DT.extension (lgManifold n)
        ((BT t).originalInclusion.map.contMDiff.mdifferentiable (by simp))
        (((jT t).comp (ET.boundaryInclusion.comp kT)).map.contMDiff.mdifferentiable (by simp))]
      rfl
  have hEne : (H.pair parameterOne).ambientDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hEH
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp (AH parameterOne).image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  have hDne : (H.pair parameterOne).ribbonDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hDH
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp (BH parameterOne).image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  have hcommonE : (JH parameterOne).map '' (H.pair parameterOne).ambientDomain.domain.carrier =
      (JT parameterZero).map '' (T.pair parameterZero).ambientDomain.domain.carrier := by
    rw [(hdataH parameterOne).1, (hdataT parameterZero).1]
    ext y
    simp only [parameterOne, parameterZero, potentialPath_one_eq_tailoringRounded_zero,
      tailoringRoundedDomain, tailoringRoundedDefiningFunction]
  have hcommonR : (RH parameterOne).map '' (H.pair parameterOne).ribbonDomain.domain.carrier =
      (RT parameterZero).map '' (T.pair parameterZero).ribbonDomain.domain.carrier := by
    rw [(hdataH parameterOne).2.2.1, (hdataT parameterZero).2.2.1]
    simpa only [parameterOne, parameterZero, potentialPath, sub_self, zero_mul, one_mul, zero_add] using
      (tailoringFamily_zero_truncation I β Aminus (fun y => φ y.1)).symm
  have hψone : potentialPath (fun u => realSquaredNorm u / 2) φ 1 = φ := by
    funext u
    simp [potentialPath]
  let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
    (W (I.alongCoefficientPath 1)) (K / Real.exp β ^ 2)
  have hPα : (H.pair parameterOne).ambientDomain.liouville.primitive =
      (H.pair parameterOne).ambientDomain.domain.extension.pullback (lgManifold n) (JH parameterOne).map α := by
    simpa only [parameterOne, hψone] using
      (hdataH parameterOne).2.2.2.2.1
  have hQα : (T.pair parameterZero).ambientDomain.liouville.primitive =
      (T.pair parameterZero).ambientDomain.domain.extension.pullback (lgManifold n) (JT parameterZero).map α := by
    simpa only [parameterZero, tailoringFamily_zero_rankTwoPrimitive] using
      (hdataT parameterZero).2.2.2.2.1
  have hPμ : (H.pair parameterOne).ribbonDomain.liouville.primitive =
      (H.pair parameterOne).ribbonDomain.domain.extension.pullback (lgManifold n) (RH parameterOne).map
        (lambdaPotentialForm φ) := by
    simpa only [parameterOne, hψone] using
      (hdataH parameterOne).2.2.2.2.2.1
  obtain ⟨q, hscale, hshift, hsquare, hcompact⟩ :=
    CompletionIdentification.exists_of_commonEmbeddedPair (H.pair parameterOne) (T.pair parameterZero)
      hEne hDne (JH parameterOne) (JT parameterZero) hcommonE hcommonR α
      (lambdaPotentialForm φ) hPα hQα hPμ ((hdataT parameterZero).2.2.2.2.2.1)
  have hsEH := localizedCompletionFamily_isSmoothIntervalEmbeddingFamily EH
    (ΛH (K / Real.exp β ^ 2) hKH') ambientH (lgManifold n) jH _hsJH
  have hsET := localizedCompletionFamily_isSmoothIntervalEmbeddingFamily ET
    (ΛT K hKT') ambientT (lgManifold n) jT _hsJT
  have hsRH := localizedCompletionFamily_isSmoothIntervalEmbeddingFamily DH ΜH ribbonH
    (lgManifold n) (fun t => (jH t).comp (EH.boundaryInclusion.comp kH)) _hsRH
  have hsRT := localizedCompletionFamily_isSmoothIntervalEmbeddingFamily DT ΜT ribbonT
    (lgManifold n) (fun t => (jT t).comp (ET.boundaryInclusion.comp kT)) _hsRT
  have hEHlocal (t : Parameter) : (H.pair t).ambientDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hEH
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp (AH t).image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  have hDHlocal (t : Parameter) : (H.pair t).ribbonDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hDH
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp (BH t).image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  have hETlocal (t : Parameter) : (T.pair t).ambientDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hET
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp (AT t).image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  have hDTlocal (t : Parameter) : (T.pair t).ribbonDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hDT
    obtain ⟨z, hz, _⟩ := (Set.ext_iff.mp (BT t).image_originalInclusion_carrier x).mpr hx
    exact ⟨z, hz⟩
  choose NH jFH PH iFH himFH hsquareFH qFH _hendFH using hRMH
  choose NT jFT PT iFT himFT hsquareFT qFT _hendFT using hRMT
  let familyH : EmbeddedRoundedPairFamily
      (fun t y => potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y))
      (fun t => W (I.alongCoefficientPath t.val))
      (fun t => potentialPath (fun u => realSquaredNorm u / 2) φ t.val)
      (Real.exp β : ℂ) Aminus (K / Real.exp β ^ 2) :=
    { deformation := H
      embedding := JH
      ambient_nonempty := hEHlocal
      ribbon_nonempty := hDHlocal
      ambient_image := fun t => (hdataH t).1
      ambient_frontier := fun t => (hdataH t).2.1
      ribbon_image := fun t => (hdataH t).2.2.1
      ribbon_frontier := fun t => (hdataH t).2.2.2.1
      ambient_primitive := fun t => (hdataH t).2.2.2.2.1
      ribbon_primitive := fun t => (hdataH t).2.2.2.2.2.1
      witness := fun t => (hdataH t).2.2.2.2.2.2
      ambient_smooth := hsEH
      ribbon_smooth := hsRH
      ribbon_marking := fun t =>
        { manifold := NH t, embedding := jFH t, primitive := PH t, inclusion := iFH t
          image := himFH t, compact_square := hsquareFH t, marking := qFH t } }
  let familyT : EmbeddedRoundedPairFamily
      (fun t => tailoringRoundedDefiningFunction I φ β t.val (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m)
      (fun t => tailoringFamily I β t.val) (fun _ => φ) 1 Aminus K :=
    { deformation := T
      embedding := JT
      ambient_nonempty := hETlocal
      ribbon_nonempty := hDTlocal
      ambient_image := fun t => (hdataT t).1
      ambient_frontier := fun t => (hdataT t).2.1
      ribbon_image := fun t => (hdataT t).2.2.1
      ribbon_frontier := fun t => (hdataT t).2.2.2.1
      ambient_primitive := fun t => (hdataT t).2.2.2.2.1
      ribbon_primitive := fun t => (hdataT t).2.2.2.2.2.1
      witness := fun t => (hdataT t).2.2.2.2.2.2
      ambient_smooth := hsET
      ribbon_smooth := hsRT
      ribbon_marking := fun t =>
        { manifold := NT t, embedding := jFT t, primitive := PT t, inclusion := iFT t
          image := himFT t, compact_square := hsquareFT t, marking := qFT t } }
  let ambientPrimitiveH := fun t : Parameter =>
    potentialPath_W_ambientCompletePrimitive hφ hEnd1 hEnd hhom hc hlower hupper hL hend
      t.val t.property (I.alongCoefficientPath t.val) hK0
  let ambientMarkH : FullAmbientInclusionMarkingFamily H JH
      (fun t => (lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
        (W (I.alongCoefficientPath t.val)) (K / Real.exp β ^ 2)) :=
    { primitive := ambientPrimitiveH, marking := qH
      forward_smooth := hsmarkH.1, inverse_smooth := hsmarkH.2 }
  obtain ⟨hcompactT, hωT, houtT, outerT, iAT, qAT, hsquareAT, _hendAT, hsAT, hsATinv⟩ := hAMT
  let OuterT := fun (t : Parameter) => tailoringPotentialOuterDomain I hφ β t.val K
    (Cplus ^ 2 * β ^ 2 / 2) (hcompactT t) (hωT t) (houtT t)
  let Douter := regularSublevelCompactDomain (lgManifold n)
    (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
    ((contMDiff_potentialValue hφ).sub contMDiff_const) (hcompactT parameterZero)
    (regular_zero_of_scalarDerivative_pos (lgManifold n)
      (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β parameterZero.val) K)) (houtT parameterZero))
  let eqOuter := fun (t : Parameter) => tailoringPotentialOuterDomain_domain I hφ
    β t.val K (Cplus ^ 2 * β ^ 2 / 2) (hcompactT t) (hωT t) (houtT t)
  let Λouter : Parameter → LiouvilleStructure Douter := fun t =>
    LiouvilleDomain.transportLiouvilleStructure (OuterT t) Douter (eqOuter t)
  let ambientMarkT : OuterAmbientInclusionMarkingFamily T JT
      (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
      (fun t => (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) :=
    { domain := Douter
      nativeEmbedding := SmoothEmbedding.identity (lgManifold n)
      native_image := by exact Set.image_id _
      liouville := Λouter
      native_primitive := fun t => by
        change (Λouter t).primitive = (lgManifold n).pullback (lgManifold n) id _
        rw [(lgManifold n).pullback_id]
        exact eq_of_heq (LiouvilleDomain.transport_primitive_heq (OuterT t) Douter (eqOuter t))
      family := outerT
      inclusion := iAT
      marking := qAT
      compact_square := hsquareAT
      forward_smooth := hsAT
      inverse_smooth := hsATinv }
  exact ⟨{ holomorphic := familyH, tailoring := familyT
           holomorphic_ambient_marking := ambientMarkH
           tailoring_ambient_marking := ambientMarkT
           junction := q, junction_scale := hscale, junction_shift := hshift
           junction_ribbon := hsquare, junction_ambient := hcompact }⟩

/-- The toric finite input supplies the strongly compatible homogeneous
potential and every analytic hypothesis of the retained marked-prefix
construction. No potential, geometric chain or marking is assumed here. -/
theorem ToricInput.exists_uniform_marked_holomorphic_tailoring_prefix
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      (∃ L > 0,
        (∀ u, L ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) ∧
        (∀ t u, L ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ →
          potentialPath (fun u => realSquaredNorm u / 2) φ t u =
            potentialPath (fun u => realSquaredNorm u / 2) φEnd t u)) ∧
      (∀ t r : ℝ, 0 < r → ∀ u,
        potentialPath (fun u => realSquaredNorm u / 2) φEnd t (r • u) =
          r ^ 2 * potentialPath (fun u => realSquaredNorm u / 2) φEnd t u) ∧
      ContDiff ℝ ∞ (fun p : ℝ × RealSpace n =>
        potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2) ∧
      ∃ c U : ℝ, 0 < c ∧ 0 < U ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : EuclideanSpace ℝ (Fin n),
        c * ‖v‖ ^ 2 ≤ inner ℝ
          (fderiv ℝ (gradient (potentialPath (fun u => realSquaredNorm u / 2) φ t ∘
            EuclideanSpace.equiv (Fin n) ℝ)) u v) v ∧
        inner ℝ (fderiv ℝ (gradient (potentialPath (fun u => realSquaredNorm u / 2) φ t ∘
          EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) ∧
      ∃ F : ℝ, 0 < F ∧ ∀ Cplus : ℝ, F < Cplus →
        ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
        ∃ Kstar : ℝ, 0 < Kstar ∧
        ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
        ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
        ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ → ∀ K : ℝ, Kstar ≤ K →
          Nonempty (PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m) := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, ⟨L, hL, hend, hendpath⟩, hpathhom,
    hpathsmooth, c, U, hc, hU, hess⟩ := I.exists_compatiblePotential_with_uniform_path
  have hessOne := hess 1 (by simp)
  have hψone : potentialPath (fun u => realSquaredNorm u / 2) φ 1 = φ := by
    funext u
    simp [potentialPath]
  rw [hψone] at hessOne
  have hend' : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ →
      φ u = φEnd u := hend
  obtain ⟨F, hF, hfamily⟩ := coefficientPath_tailoring_exists_uniform_marked_prefix
    I hφ hc hU (fun u v => (hessOne u v).1) (fun u v => (hessOne u v).2)
    hEnd1 hstrong.smooth hstrong.homogeneous hL hend'
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, ⟨L, hL, hend, hendpath⟩, hpathhom,
    hpathsmooth, c, U, hc, hU, hess, F, hF, ?_⟩
  intro Cplus hCplus
  obtain ⟨β₀, hβ₀, hfamily⟩ := hfamily Cplus hCplus
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨Kstar, hKstar, _hpathThreshold, hfamily⟩ := hfamily β hβ
  exact ⟨Kstar, hKstar, hfamily⟩

end FsFltz
