import FsFltz.Geometry.PotentialPathRetainedRibbonMarkingFamily
import FsFltz.Geometry.PotentialPathMarkingFamilySmooth

/-!
# Smooth inclusion markings on the same actual holomorphic pair

Source: geometric-part-fsf-proof.tex, lem:markedfamily, lines 975–1049,
smooth completion markings, lines 1270–1314, and lem:grading, lines
1981–1992. The exact retained pair, its compact images and both pointwise
full-fiber markings are retained; ambient forward and inverse real smooth
germs are proved from their actual primitives and compact inclusion squares.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set
namespace FsFltz
open Geometry
variable {n : ℕ}

/-- The same actual retained holomorphic pair has selected ambient inclusion
markings whose forward and inverse maps have real smooth germs, while retaining
both actual pointwise whole-fiber ribbon markings and every presentation square. -/
theorem coefficientPath_potentialPath_exists_uniform_rounded_pairDeformation_with_smooth_markings
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
            (∀ t : Parameter,
              ((J t).comp (A t).originalInclusion).map '' (A t).localizedDomain.domain.carrier =
                {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) ≤ 0} ∧
              ((J t).comp (A t).originalInclusion).map '' frontier (A t).localizedDomain.domain.carrier =
                {y | potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) = 0} ∧
              ((jR t).comp (B t).originalInclusion).map '' (B t).localizedDomain.domain.carrier =
                {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
              ((jR t).comp (B t).originalInclusion).map '' frontier (B t).localizedDomain.domain.carrier =
                {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus} ) ∧
            ∃ hK0 : 0 ≤ K,
              ∃ q : (t : Parameter) → InclusionMarking (A t).cylindricalCompletion
                (potentialPath_W_ambientCompletePrimitive hφ hEnd1 hEnd hhom hc
                  hlower hupper hL hend t.val t.property (I.alongCoefficientPath t.val)
                  hK0).toCompleteLiouvilleManifold
                (fun x => (J t).map ((A t).originalInclusion.map x.val)),
              (let M := (A parameterZero).cylindricalCompletion.ambient.manifold
               let f := fun t => (ambient.completionPresentation t).equiv.trans (q t).equiv
               IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn M (lgManifold n) univ
                 (fun t => f t) ∧
               IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn (lgManifold n) M univ
                 (fun t => (f t).symm)) ∧
              (∀ t : Parameter,
                ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
                  (P : CompletePrimitive N (N.pullback (lgManifold n) j.map
                    (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))))
                  (i : (B t).localizedDomain.domain.Point → N.Point),
                  range j.map = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ)} ∧
                  (∀ x, j.map (i x) = (jR t).map ((B t).originalInclusion.map x.val)) ∧
                  ∃ q : InclusionMarking (B t).cylindricalCompletion P.toCompleteLiouvilleManifold i,
                    ∀ b r, q.equiv ((B t).cylindricalCompletion.endMap (b, r)) =
                      P.completeFlow.flow r (i ⟨(B t).localizedDomain.domain.boundaryInclusion.map b,
                        (B t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩)) := by
  classical
  obtain ⟨F, hF, hfamily⟩ :=
    coefficientPath_potentialPath_exists_uniform_rounded_pairDeformation_with_markings
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, ?_⟩
  intro Cplus hCplus
  obtain ⟨β₀, hβ₀, hfamily⟩ := hfamily Cplus hCplus
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨Kstar, hKstar, hthreshold, hfamily⟩ := hfamily β hβ
  refine ⟨Kstar, hKstar, hthreshold, ?_⟩
  intro Aminus hlo hhi
  obtain ⟨δ, hδ, hδgap, hfamily⟩ := hfamily Aminus hlo hhi
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmδ
  obtain ⟨E, D, k, J, Λ, Μ, hE, hD, hJ, hR, himages, hΛ, hΜ, hfamily⟩ :=
    hfamily m hm hmδ
  refine ⟨E, D, k, J, Λ, Μ, hE, hD, hJ, hR, himages, hΛ, hΜ, ?_⟩
  intro K hK
  obtain ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, hQ, hpairs, hlocal,
    hK0, hambient, hribbonMark⟩ := hfamily K hK
  let A := ambient.collars
  let η : Parameter → (lgManifold n).Form 1 := fun t =>
    (lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
      (W (I.alongCoefficientPath t.val)) K
  let P (t : Parameter) : CompletePrimitive (lgManifold n) (η t) :=
    potentialPath_W_ambientCompletePrimitive hφ hEnd1 hEnd hhom hc
      hlower hupper hL hend t.val t.property (I.alongCoefficientPath t.val) hK0
  let q : (t : Parameter) → InclusionMarking (A t).cylindricalCompletion
      (P t).toCompleteLiouvilleManifold
      (fun x => (J t).map ((A t).originalInclusion.map x.val)) :=
    fun t => Classical.choice (hambient t)
  have hη : (lgManifold n).IsSmoothIntervalFormFamily η :=
    ⟨fun t => (lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t))
      (W (I.alongCoefficientPath t)) K,
      isSmoothFormFamily_coefficientPath_potentialPath_primitive I hφ K,
      fun _ => rfl⟩
  have hsquare : ∀ t x, x ∈ (A t).localizedDomain.domain.carrier →
      (q t).equiv x = (J t).map ((A t).originalInclusion.map x) := by
    intro t x hx
    exact (q t).inclusion ⟨x, hx⟩
  have hregular := ambient.markingFamily_realGerms_into_fixed_ambient
    (lgManifold n) η P hη (fun t => (J t).map) hJ
    (fun t => (q t).equiv) (fun t => (q t).primitive) hsquare
  exact ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, hQ, hpairs,
    hlocal, hK0, q, hregular, hribbonMark⟩

end FsFltz
