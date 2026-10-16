import FsFltz.Geometry.PotentialPathRoundedPairFamily
import FsFltz.Geometry.TailoringNormalizedEndpointIdentification
import FsFltz.Geometry.EmbeddedCarrierCompactMap

/-!
# The actual normalized holomorphic-to-tailoring junction

Source: `geometric-part-fsf-proof.tex`, `eq:normalizedrounding`, lines
1260–1262, common markings, lines 1270–1314, and assembly, lines
2148–2158; `geoemtric-part-fsf.tex`, `def:chain`, lines 163–200.
The full common embedded carriers construct the compact maps between
independently constructed pairs, then their chosen completions are compared.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.CompletionIdentification
open SmoothManifold

/-- Equal full embedded carriers and literal common-form pullbacks
construct the strict completed pair comparison, including for rank one.
No compact or completed equivalence is assumed. -/
theorem exists_of_commonEmbeddedPair {n : ℕ} (P Q : WitnessedPair n)
    (hE : P.ambientDomain.domain.carrier.Nonempty)
    (hD : P.ribbonDomain.domain.carrier.Nonempty)
    (J : P.ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (K : Q.ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (hambient : J.map '' P.ambientDomain.domain.carrier = K.map '' Q.ambientDomain.domain.carrier)
    (hribbon : (J.comp (P.ambientDomain.domain.boundaryInclusion.comp P.ribbonEmbedding)).map ''
        P.ribbonDomain.domain.carrier =
      (K.comp (Q.ambientDomain.domain.boundaryInclusion.comp Q.ribbonEmbedding)).map ''
        Q.ribbonDomain.domain.carrier)
    (α μ : (lgManifold n).Form 1)
    (hPα : P.ambientDomain.liouville.primitive =
      P.ambientDomain.domain.extension.pullback (lgManifold n) J.map α)
    (hQα : Q.ambientDomain.liouville.primitive =
      Q.ambientDomain.domain.extension.pullback (lgManifold n) K.map α)
    (hPμ : P.ribbonDomain.liouville.primitive =
      P.ribbonDomain.domain.extension.pullback (lgManifold n)
        (J.comp (P.ambientDomain.domain.boundaryInclusion.comp P.ribbonEmbedding)).map μ)
    (hQμ : Q.ribbonDomain.liouville.primitive =
      Q.ribbonDomain.domain.extension.pullback (lgManifold n)
        (K.comp (Q.ambientDomain.domain.boundaryInclusion.comp Q.ribbonEmbedding)).map μ) :
    ∃ I : CompletionIdentification P Q,
      I.scale = 1 ∧ I.shift = (fun _ => 0) ∧
      (∀ x ∈ P.ribbonDomain.domain.carrier,
        (K.comp (Q.ambientDomain.domain.boundaryInclusion.comp Q.ribbonEmbedding)).map
          (I.ribbonEquiv.map x) =
        (J.comp (P.ambientDomain.domain.boundaryInclusion.comp P.ribbonEmbedding)).map x) ∧
      (∀ x ∈ P.ambientDomain.domain.carrier,
        ∃ y ∈ Q.ambientDomain.domain.carrier, K.map y = J.map x ∧
          I.ambientEquiv (P.ambientCompletion.inclusion.map x) =
            Q.ambientCompletion.inclusion.map y) := by
  let R := J.comp (P.ambientDomain.domain.boundaryInclusion.comp P.ribbonEmbedding)
  let S := K.comp (Q.ambientDomain.domain.boundaryInclusion.comp Q.ribbonEmbedding)
  obtain ⟨a, ha, _⟩ := CompactDomain.exists_compactDiffeomorph_of_commonEmbedding
    P.ambientDomain.domain Q.ambientDomain.domain (lgManifold n) hE J K hambient
  obtain ⟨g, hg, _⟩ := CompactDomain.exists_compactDiffeomorph_of_embeddedCarrier
    P.ribbonDomain.domain Q.ribbonDomain.domain (lgManifold n) hD R S hribbon
  have hpa (x) (hx : x ∈ P.ambientDomain.domain.carrier) :
      P.ambientDomain.domain.extension.pullback Q.ambientDomain.domain.extension a.map
        Q.ambientDomain.liouville.primitive x = P.ambientDomain.liouville.primitive x := by
    rw [hPα, hQα]
    exact a.pullback_of_commonEmbedding (lgManifold n) J K ha α x hx
  have hpg (x) (hx : x ∈ P.ribbonDomain.domain.carrier) :
      P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension g.map
        Q.ribbonDomain.liouville.primitive x = (1 : ℝ) • P.ribbonDomain.liouville.primitive x := by
    rw [one_smul, hPμ, hQμ]
    exact g.pullback_of_embeddedCarrier (lgManifold n) R S hg μ x hx
  have hsquare (x) (hx : x ∈ P.ribbonDomain.domain.carrier) :
      a.map (P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x)) =
        Q.ambientDomain.domain.boundaryInclusion.map (Q.ribbonEmbedding.map (g.map x)) := by
    apply K.embedding.injective
    have hp : P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x) ∈
        P.ambientDomain.domain.carrier :=
      P.ambientDomain.domain.boundaryInclusion_mem_carrier _
    rw [ha _ (a.contains_source hp)]
    exact (hg x hx).symm
  obtain ⟨I, hIg, hIc, hIs, hIa⟩ := exists_of_compactPairSquare
    P Q a g hpa 1 zero_lt_one hpg hsquare
  refine ⟨I, hIc, hIs, ?_, ?_⟩
  · intro x hx
    rw [hIg]
    exact hg x hx
  · intro x hx
    exact ⟨a.map x, a.maps_source hx, ha x (a.contains_source hx), hIa x hx⟩

end FsFltz.Geometry.CompletionIdentification

namespace FsFltz
open Geometry SmoothManifold
variable {n : ℕ}

/-- The actual compact presentation transports a smooth native embedding
family to a smooth family on the one localized base extension. -/
theorem localizedCompletionFamily_isSmoothIntervalEmbeddingFamily {d e : ℕ}
    (D : CompactDomain d) (Λ : Parameter → LiouvilleStructure D)
    (C : LocalizedCompletionFamily D Λ) (M : SmoothManifold e)
    (J : Parameter → D.extension.SmoothEmbedding M)
    (hJ : D.extension.IsSmoothIntervalMapFamily M (fun t => (J t).map)) :
    (C.collars parameterZero).localizedDomain.domain.extension.IsSmoothIntervalMapFamily M
      (fun t x => (J t).map ((C.collars t).originalInclusion.map
        ((C.compactPresentation t).extensionEquiv x))) := by
  let E := (C.collars parameterZero).localizedDomain.domain.extension
  let k := fun (t : ℝ) (x : E.Point) =>
    (C.originalPresentation t).extensionEquiv ((C.collars parameterZero).originalInclusion.map x)
  have hk : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × E.Point => k p.1 p.2) :=
    C.smooth_originalPresentation.comp (contMDiff_fst.prodMk
      ((C.collars parameterZero).originalInclusion.map.contMDiff.comp contMDiff_snd))
  have hs := E.isSmoothIntervalMapFamily_comp_of_contMDiff_family D.extension M
    (fun t => (J t).map) hJ k hk
  convert hs using 1
  funext t x
  change (J t).map (((C.compactPresentation t).extensionEquiv x).val.val) = _
  rw [C.original_projection]
  rfl

/-- The same retained profile makes the actual two endpoint scalars equal. -/
theorem potentialPath_one_eq_tailoringRounded_zero (I : ToricInput n)
    (φ : RealSpace n → ℝ) (β A : ℝ) (m : RoundingChoice) (y : LGSpace n) :
    potentialPath_roundedDefiningFunction I φ (Real.exp β) A m (1, y) =
      tailoringRoundedDefiningFunction I φ β 0 (Real.exp β) A m y := by
  simpa only [potentialPath_roundedDefiningFunction, tailoringRoundedDefiningFunction,
    potentialPath, sub_self, zero_mul, one_mul, zero_add] using
    (tailoringFamily_zero_normalized_rounding I β A (fun y => φ y.1) m y).symm


/-- Finite input constructs both complete pair families at one retained
profile and their actual strict normalized junction. All whole/frontier
images, primitives and constant-one witnesses are retained for the full
families, so the produced identification can be inserted into a chain. -/
theorem coefficientPath_tailoring_exists_uniform_normalized_pair_junction_with_smooth_embeddings
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
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ → ∀ K : ℝ, Kstar ≤ K →
      ∃ (H T : PairDeformation n)
        (JH : (t : Parameter) → (H.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
        (JT : (t : Parameter) → (T.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
        (q : CompletionIdentification (H.pair parameterOne) (T.pair parameterZero)),
        let RH := fun t => (JH t).comp
          ((H.pair t).ambientDomain.domain.boundaryInclusion.comp (H.pair t).ribbonEmbedding)
        let RT := fun t => (JT t).comp
          ((T.pair t).ambientDomain.domain.boundaryInclusion.comp (T.pair t).ribbonEmbedding)
        (∀ t : Parameter,
          (JH t).map '' (H.pair t).ambientDomain.domain.carrier =
            {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) ≤ 0} ∧
          (JH t).map '' frontier (H.pair t).ambientDomain.domain.carrier =
            {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) = 0} ∧
          (RH t).map '' (H.pair t).ribbonDomain.domain.carrier =
            {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
              potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
          (RH t).map '' frontier (H.pair t).ribbonDomain.domain.carrier =
            {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
              potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus} ∧
          (H.pair t).ambientDomain.liouville.primitive =
            (H.pair t).ambientDomain.domain.extension.pullback (lgManifold n) (JH t).map
              ((lgManifold n).rankTwoPrimitive
                (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
                (W (I.alongCoefficientPath t.val)) (K / Real.exp β ^ 2)) ∧
          (H.pair t).ribbonDomain.liouville.primitive =
            (H.pair t).ribbonDomain.domain.extension.pullback (lgManifold n) (RH t).map
              (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)) ∧
          (H.pair t).witness = (fun _ => 1)) ∧
        (∀ t : Parameter,
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
            (T.pair t).ribbonDomain.domain.extension.pullback (lgManifold n) (RT t).map
              (lambdaPotentialForm φ) ∧
          (T.pair t).witness = (fun _ => 1)) ∧
        q.scale = 1 ∧ q.shift = (fun _ => 0) ∧
        (∀ x ∈ (H.pair parameterOne).ribbonDomain.domain.carrier,
          (RT parameterZero).map (q.ribbonEquiv.map x) = (RH parameterOne).map x) ∧
        (∀ x ∈ (H.pair parameterOne).ambientDomain.domain.carrier,
          ∃ y ∈ (T.pair parameterZero).ambientDomain.domain.carrier,
            (JT parameterZero).map y = (JH parameterOne).map x ∧
            q.ambientEquiv ((H.pair parameterOne).ambientCompletion.inclusion.map x) =
              (T.pair parameterZero).ambientCompletion.inclusion.map y) ∧
        (H.pair parameterZero).ambientDomain.domain.extension.IsSmoothIntervalMapFamily (lgManifold n)
          (fun t x => (JH t).map ((H.ambientPresentation t).extensionEquiv x)) ∧
        (T.pair parameterZero).ambientDomain.domain.extension.IsSmoothIntervalMapFamily (lgManifold n)
          (fun t x => (JT t).map ((T.ambientPresentation t).extensionEquiv x)) ∧
        (H.pair parameterZero).ribbonDomain.domain.extension.IsSmoothIntervalMapFamily (lgManifold n)
          (fun t x => (RH t).map ((H.ribbonPresentation t).extensionEquiv x)) ∧
        (T.pair parameterZero).ribbonDomain.domain.extension.IsSmoothIntervalMapFamily (lgManifold n)
          (fun t x => (RT t).map ((T.ribbonPresentation t).extensionEquiv x)) := by
  classical
  obtain ⟨FH, hFH, hhol⟩ :=
    coefficientPath_potentialPath_exists_uniform_rounded_pairDeformation_with_presentations
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨FT, hFT, htail⟩ :=
    tailoringFamily_exists_uniform_rounded_pairDeformation_with_presentations
      I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  let F := max FH FT
  refine ⟨F, hFH.trans_le (le_max_left _ _), ?_⟩
  intro Cplus hCplus
  obtain ⟨BH, hBH, hhol⟩ := hhol Cplus ((le_max_left _ _).trans_lt hCplus)
  obtain ⟨BT, hBT, htail⟩ := htail Cplus ((le_max_right _ _).trans_lt hCplus)
  refine ⟨max BH BT, hBH.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨KH, hKH, _hthreshold, hhol⟩ := hhol β ((le_max_left _ _).trans hβ)
  obtain ⟨KT, hKT, htail⟩ := htail β ((le_max_right _ _).trans hβ)
  let Kstar := max (KH * Real.exp β ^ 2) KT
  refine ⟨Kstar, hKT.trans_le (le_max_right _ _), ?_⟩
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
  obtain ⟨hrH, hαH, hμH, hkH, hbH, ambientH, ribbonH, H, heH, _hpH, hlocH⟩ :=
    hcompleteH (K / Real.exp β ^ 2) hKH'
  obtain ⟨hrT, hαT, hμT, hkT, hbT, ambientT, ribbonT, T, heT, _hpT, hlocT⟩ :=
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
  refine ⟨H, T, JH, JT, q, hdataH, hdataT, hscale, hshift, hsquare, hcompact, hsEH, hsET, ?_, ?_⟩
  · exact hsRH
  · exact hsRT

/-- The normalized junction with its literal whole family payload. The
stronger producer additionally retains joint smoothness of the embedding
families under these very compact presentation maps. -/
theorem coefficientPath_tailoring_exists_uniform_normalized_pair_junction
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
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ → ∀ K : ℝ, Kstar ≤ K →
      ∃ (H T : PairDeformation n)
        (JH : (t : Parameter) → (H.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
        (JT : (t : Parameter) → (T.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
        (q : CompletionIdentification (H.pair parameterOne) (T.pair parameterZero)),
        let RH := fun t => (JH t).comp
          ((H.pair t).ambientDomain.domain.boundaryInclusion.comp (H.pair t).ribbonEmbedding)
        let RT := fun t => (JT t).comp
          ((T.pair t).ambientDomain.domain.boundaryInclusion.comp (T.pair t).ribbonEmbedding)
        (∀ t : Parameter,
          (JH t).map '' (H.pair t).ambientDomain.domain.carrier =
            {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) ≤ 0} ∧
          (JH t).map '' frontier (H.pair t).ambientDomain.domain.carrier =
            {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) = 0} ∧
          (RH t).map '' (H.pair t).ribbonDomain.domain.carrier =
            {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
              potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
          (RH t).map '' frontier (H.pair t).ribbonDomain.domain.carrier =
            {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
              potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus} ∧
          (H.pair t).ambientDomain.liouville.primitive =
            (H.pair t).ambientDomain.domain.extension.pullback (lgManifold n) (JH t).map
              ((lgManifold n).rankTwoPrimitive
                (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
                (W (I.alongCoefficientPath t.val)) (K / Real.exp β ^ 2)) ∧
          (H.pair t).ribbonDomain.liouville.primitive =
            (H.pair t).ribbonDomain.domain.extension.pullback (lgManifold n) (RH t).map
              (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)) ∧
          (H.pair t).witness = (fun _ => 1)) ∧
        (∀ t : Parameter,
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
            (T.pair t).ribbonDomain.domain.extension.pullback (lgManifold n) (RT t).map
              (lambdaPotentialForm φ) ∧
          (T.pair t).witness = (fun _ => 1)) ∧
        q.scale = 1 ∧ q.shift = (fun _ => 0) ∧
        (∀ x ∈ (H.pair parameterOne).ribbonDomain.domain.carrier,
          (RT parameterZero).map (q.ribbonEquiv.map x) = (RH parameterOne).map x) ∧
        ∀ x ∈ (H.pair parameterOne).ambientDomain.domain.carrier,
          ∃ y ∈ (T.pair parameterZero).ambientDomain.domain.carrier,
            (JT parameterZero).map y = (JH parameterOne).map x ∧
            q.ambientEquiv ((H.pair parameterOne).ambientCompletion.inclusion.map x) =
              (T.pair parameterZero).ambientCompletion.inclusion.map y := by
  obtain ⟨F, hF, hfamilies⟩ := coefficientPath_tailoring_exists_uniform_normalized_pair_junction_with_smooth_embeddings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, ?_⟩
  intro Cplus hCplus
  obtain ⟨β₀, hβ₀, hfamilies⟩ := hfamilies Cplus hCplus
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨Kstar, hKstar, hfamilies⟩ := hfamilies β hβ
  refine ⟨Kstar, hKstar, ?_⟩
  intro Aminus hlo hhi
  obtain ⟨δ, hδ, hgap, hfamilies⟩ := hfamilies Aminus hlo hhi
  refine ⟨δ, hδ, hgap, ?_⟩
  intro m hm hmd K hK
  obtain ⟨H, T, JH, JT, q, hH, hT, hscale, hshift, hribbon, hambient, _hsmooth⟩ :=
    hfamilies m hm hmd K hK
  exact ⟨H, T, JH, JT, q, hH, hT, hscale, hshift, hribbon, hambient⟩

end FsFltz
