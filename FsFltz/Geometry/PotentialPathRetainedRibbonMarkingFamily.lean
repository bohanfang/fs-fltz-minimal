import FsFltz.Geometry.PotentialPathRetainedRibbonMarking
import FsFltz.Geometry.PotentialPathRoundedMarking

/-!
# Both actual inclusion markings on the same holomorphic rounded pair

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1049,
and assembly, lines 2127–2158. Both pointwise markings are added to the
exact retained pair deformation and its supplied cylindrical completions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- Add both actual pointwise inclusion markings to the same retained holomorphic pair. -/
theorem coefficientPath_potentialPath_exists_uniform_rounded_pairDeformation_with_markings
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
              (∀ t : Parameter,
                let P := (potentialPath_W_ambientCompletePrimitive hφ hEnd1 hEnd hhom hc
                  hlower hupper hL hend t.val t.property (I.alongCoefficientPath t.val)
                  hK0).toCompleteLiouvilleManifold
                Nonempty (InclusionMarking (A t).cylindricalCompletion P
                  (fun x => (J t).map ((A t).originalInclusion.map x.val)))) ∧
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
  obtain ⟨Fp, hFp, hpair⟩ := coefficientPath_potentialPath_exists_uniform_rounded_pairDeformation_with_presentations
    I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fr, hFr, Br, hBr, hmark⟩ :=
    Geometry.ToricInput.coefficientPath_potentialPath_exists_uniform_retainedRibbon_markings
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨A₀, R₀, hA₀, hR₀, hambient⟩ :=
    Geometry.ToricInput.coefficientPath_potentialPath_exists_rounded_ambient_markings
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  let F := max Fp (max Fr 1)
  have hF : 0 < F := hFp.trans_le (le_max_left _ _)
  refine ⟨F, hF, ?_⟩
  intro Cplus hCF
  obtain ⟨Bp, hBp, hpair⟩ := hpair Cplus ((le_max_left _ _).trans_lt hCF)
  let β₀ := max Bp (max Br (max R₀ (4 * A₀ + 1)))
  refine ⟨β₀, hBp.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβp : Bp ≤ β := (le_max_left _ _).trans hβ
  have hβr : Br ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβR : R₀ ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβA : 4 * A₀ + 1 ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hR : R₀ ≤ Real.exp β := by linarith [Real.add_one_le_exp β]
  have hCone : 1 ≤ Cplus :=
    ((le_max_right Fr 1).trans (le_max_right Fp (max Fr 1))).trans hCF.le
  have hA : 2 * A₀ ≤ Cplus ^ 2 * β ^ 2 / 2 := by
    have hβone : 1 ≤ β := by linarith
    have hβsq : β ≤ β ^ 2 := by nlinarith
    have hCsq : 1 ≤ Cplus ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hCsq (sq_nonneg β)]
  obtain ⟨Kp, hKp, hKpath, hpair⟩ := hpair β hβp
  obtain ⟨Ka, hKa, hambient⟩ := hambient (Real.exp β) hR
  let Kstar := max Kp Ka
  refine ⟨Kstar, hKp.trans_le (le_max_left _ _), hKpath.trans (le_max_left _ _), ?_⟩
  intro Aminus hlo hhi
  have hFpA : Fp ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlo
    gcongr
    exact le_max_left Fp (max Fr 1)
  have hFrA : Fr ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlo
    gcongr
    exact (le_max_left Fr 1).trans (le_max_right Fp (max Fr 1))
  obtain ⟨δp, hδp, hgap, hpair⟩ := hpair Aminus hFpA hhi
  obtain ⟨δa, hδa, _hgapa, hambient⟩ := hambient (Cplus ^ 2 * β ^ 2 / 2) hA Aminus hhi
  refine ⟨min δp δa, lt_min hδp hδa, (min_le_left _ _).trans_lt hgap, ?_⟩
  intro m hm hmd
  obtain ⟨E, D, k, J, Λ, Μ, hE, hD, hJ, hRfamily, himages, hΛ, hΜ, hpair⟩ :=
    hpair m hm (hmd.trans (min_le_left _ _))
  let jR := fun t => (J t).comp (E.boundaryInclusion.comp k)
  let Λ' : (K : ℝ) → Kstar ≤ K → Parameter → LiouvilleStructure E :=
    fun K hK => Λ K ((le_max_left _ _).trans hK)
  refine ⟨E, D, k, J, Λ', Μ, hE, hD, hJ, hRfamily, himages,
    (fun K hK t => hΛ K ((le_max_left _ _).trans hK) t), hΜ, ?_⟩
  intro K hK
  have hKp' : Kp ≤ K := (le_max_left _ _).trans hK
  have hKa' : Ka ≤ K := (le_max_right _ _).trans hK
  obtain ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, hQ, hpairs, hlocal⟩ := hpair K hKp'
  let A := ambient.collars
  let B := ribbon.collars
  obtain ⟨hK0, hambmark⟩ := hambient m hm (hmd.trans (min_le_right _ _)) K hKa'
  refine ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, hQ, hpairs, hlocal, hK0, ?_, ?_⟩
  · intro t
    have hElocal : (A t).localizedDomain.domain.carrier.Nonempty := by
      obtain ⟨x, hx⟩ := hE
      have hy : (J t).map x ∈ {y | potentialPath_roundedDefiningFunction I φ (Real.exp β)
          (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y) ≤ 0} := by
        rw [← (himages t).1]
        exact ⟨x, hx, rfl⟩
      rw [← (hlocal t).1] at hy
      obtain ⟨z, hz, _he⟩ := hy
      exact ⟨z, hz⟩
    have hprimitiveLocal (x) (_hx : x ∈ (A t).localizedDomain.domain.carrier) :
        (A t).localizedDomain.liouville.primitive x =
          (A t).localizedDomain.domain.extension.pullback (lgManifold n)
            ((J t).comp (A t).originalInclusion).map
            ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
              (W (I.alongCoefficientPath t.val)) K) x := by
      rw [(A t).localized_primitive_pullback, hΛ K hKp' t]
      exact congrFun ((A t).localizedDomain.domain.extension.pullback_comp E.extension (lgManifold n)
        ((A t).originalInclusion.map.contMDiff.mdifferentiable (by simp))
        ((J t).map.contMDiff.mdifferentiable (by simp)) _).symm x
    exact hambmark t (A t).localizedDomain (A t).cylindricalCompletion hElocal
      ((J t).comp (A t).originalInclusion) (hlocal t).1 hprimitiveLocal
  · intro t
    have hDlocal : (B t).localizedDomain.domain.carrier.Nonempty := by
      obtain ⟨x, hx⟩ := hD
      have hy : (jR t).map x ∈ {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
          potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} := by
        rw [← (himages t).2.2.1]
        exact ⟨x, hx, rfl⟩
      rw [← (hlocal t).2.2.1] at hy
      obtain ⟨z, hz, _he⟩ := hy
      exact ⟨z, hz⟩
    have hμlocal (x) (_hx : x ∈ (B t).localizedDomain.domain.carrier) :
        (B t).localizedDomain.liouville.primitive x =
          (B t).localizedDomain.domain.extension.pullback (lgManifold n)
            ((jR t).comp (B t).originalInclusion).map
            (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)) x := by
      rw [(B t).localized_primitive_pullback, hΜ t]
      exact congrFun ((B t).localizedDomain.domain.extension.pullback_comp D.extension (lgManifold n)
        ((B t).originalInclusion.map.contMDiff.mdifferentiable (by simp))
        ((jR t).map.contMDiff.mdifferentiable (by simp)) _).symm x
    exact hmark β hβr t.val t.property Aminus hFrA (B t).localizedDomain hDlocal
      ((jR t).comp (B t).originalInclusion) (hlocal t).2.2.1 hμlocal (B t).cylindricalCompletion

end FsFltz
