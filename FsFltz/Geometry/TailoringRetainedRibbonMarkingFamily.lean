import FsFltz.Geometry.TailoringRetainedRibbonMarking

/-!
# The actual rounded tailoring pair with full-fiber ribbon markings

Source: `geometric-part-fsf-proof.tex`, `eq:fiberends`, lines 1208–1237,
and the marked family, lines 1304–1314. The ambient markings retain their
proved smooth family. Pointwise full-fiber ribbon markings are added to
the very same supplied pair deformation and ribbon completions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- Add full-fiber ribbon markings to the exact previously constructed rounded pair family. -/
theorem tailoringFamily_exists_uniform_rounded_pairDeformation_with_fullFiber_ribbon_markings
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
            (∀ t : Parameter,
              ((J t).comp (A t).originalInclusion).map '' (A t).localizedDomain.domain.carrier =
                tailoringRoundedDomain I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m ∧
              ((J t).comp (A t).originalInclusion).map '' frontier (A t).localizedDomain.domain.carrier =
                {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
              ((W t).comp (B t).originalInclusion).map '' (B t).localizedDomain.domain.carrier =
                {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
              ((W t).comp (B t).originalInclusion).map '' frontier (B t).localizedDomain.domain.carrier =
                {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus}) ∧
            (∀ t : Parameter,
              ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
                (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
                (i : (B t).localizedDomain.domain.Point → N.Point),
                range j.map = {y | tailoringFamily I β t.val y = 1} ∧
                (∀ x, j.map (i x) = (W t).map ((B t).originalInclusion.map x.val)) ∧
                ∃ q : InclusionMarking (B t).cylindricalCompletion P.toCompleteLiouvilleManifold i,
                  ∀ b r, q.equiv ((B t).cylindricalCompletion.endMap (b, r)) =
                    P.completeFlow.flow r (i ⟨(B t).localizedDomain.domain.boundaryInclusion.map b,
                      (B t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩)) ∧
              ∃ (hcompact : ∀ _t : Parameter,
                  IsCompact {y : LGSpace n | φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0})
                (hω : ∀ t : Parameter, (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β t.val) K)) univ)
                (hout : ∀ (t : Parameter) (y : (lgManifold n).Point), φ y.1 - Cplus ^ 2 * β ^ 2 / 2 = 0 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) y)),
              let Outer := fun (t : Parameter) => tailoringPotentialOuterDomain I hφ β t.val K
                (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
              let H := regularSublevelCompactDomain (lgManifold n)
                (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
                ((contMDiff_potentialValue hφ).sub contMDiff_const) (hcompact parameterZero)
                (regular_zero_of_scalarDerivative_pos (lgManifold n)
                  (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
                  ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                    (lambdaPotentialForm φ) (tailoringFamily I β parameterZero.val) K)) (hout parameterZero))
              let domainEq := fun (t : Parameter) => tailoringPotentialOuterDomain_domain I hφ
                β t.val K (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
              let μ : Parameter → LiouvilleStructure H := fun t =>
                LiouvilleDomain.transportLiouvilleStructure (Outer t) H (domainEq t)
              ∃ (outer : LocalizedCompletionFamily H μ)
                (i : ∀ t, (A t).localizedDomain.domain.Point →
                  (outer.collars t).cylindricalCompletion.ambient.manifold.Point)
                (q : ∀ t, InclusionMarking (A t).cylindricalCompletion
                  (outer.collars t).cylindricalCompletion.ambient (i t)),
                (∀ t x, (outer.collars t).originalInclusion.map (i t x) =
                  (J t).map ((A t).originalInclusion.map x.val)) ∧
                (∀ t b r, (q t).equiv ((A t).cylindricalCompletion.endMap (b, r)) =
                  (outer.collars t).cylindricalCompletion.ambient.completeFlow.flow r
                    (i t ⟨(A t).localizedDomain.domain.boundaryInclusion.map b,
                      (A t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩)) ∧
                let M := (A parameterZero).cylindricalCompletion.ambient.manifold
                let N := (outer.collars parameterZero).cylindricalCompletion.ambient.manifold
                let f := fun t => ((ambient.completionPresentation t).equiv.trans (q t).equiv).trans
                  (outer.completionPresentation t).equiv.symm
                IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn M N univ (fun t => f t) ∧
                  IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn N M univ (fun t => (f t).symm) := by
  obtain ⟨Fp, hFp, hpair⟩ := tailoringFamily_exists_uniform_rounded_pairDeformation_with_smooth_inclusion_markings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fr, hFr, Br, hBr, hmark⟩ := tailoringFamily_exists_uniform_retainedRibbon_fullFiber_markings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  let F := max Fp Fr
  have hF : 0 < F := hFp.trans_le (le_max_left _ _)
  refine ⟨F, hF, ?_⟩
  intro Cplus hCplus
  obtain ⟨Bp, hBp, hpair⟩ := hpair Cplus ((le_max_left _ _).trans_lt hCplus)
  refine ⟨max Bp Br, hBp.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβp : Bp ≤ β := (le_max_left _ _).trans hβ
  have hβr : Br ≤ β := (le_max_right _ _).trans hβ
  obtain ⟨Kstar, hKstar, hpair⟩ := hpair β hβp
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hlo hhi
  have hFpA : Fp ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    have hsq : Fp ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ hFp.le (le_max_left _ _) 2
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsq (sq_nonneg β)) (by norm_num)).trans hlo
  have hFrA : Fr ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    have hsq : Fr ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ hFr.le (le_max_right _ _) 2
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsq (sq_nonneg β)) (by norm_num)).trans hlo
  obtain ⟨δ, hδ, hgap, hpair⟩ := hpair R hR Aminus hFpA hhi
  refine ⟨δ, hδ, hgap, ?_⟩
  intro m hm hmδ
  obtain ⟨E, D, k, J, Λ, Μ, hE, hD, hJ, hW, himages, hΛ, hΜ, hpair⟩ := hpair m hm hmδ
  let W := fun t => (J t).comp (E.boundaryInclusion.comp k)
  refine ⟨E, D, k, J, Λ, Μ, hE, hD, hJ, hW, himages, hΛ, hΜ, ?_⟩
  intro K hK
  obtain ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, hQ, hpairs, hlocal, houter⟩ := hpair K hK
  let A := ambient.collars
  let B := ribbon.collars
  refine ⟨hribbon, hα, hμ, hk, hb, ambient, ribbon, Q, hQ, hpairs, hlocal, ?_, houter⟩
  intro t
  have hDlocal : (B t).localizedDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hD
    have hy : (W t).map x ∈ {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} := by
      rw [← (himages t).2.2.1]
      exact ⟨x, hx, rfl⟩
    rw [← (hlocal t).2.2.1] at hy
    obtain ⟨z, hz, _he⟩ := hy
    exact ⟨z, hz⟩
  have hμlocal (x) (_hx : x ∈ (B t).localizedDomain.domain.carrier) :
      (B t).localizedDomain.liouville.primitive x =
        (B t).localizedDomain.domain.extension.pullback (lgManifold n)
          ((W t).comp (B t).originalInclusion).map (lambdaPotentialForm φ) x := by
    rw [(B t).localized_primitive_pullback, hΜ t]
    exact congrFun ((B t).localizedDomain.domain.extension.pullback_comp D.extension (lgManifold n)
      ((B t).originalInclusion.map.contMDiff.mdifferentiable (by simp))
      ((W t).map.contMDiff.mdifferentiable (by simp)) (lambdaPotentialForm φ)).symm x
  exact hmark β hβr t.val t.property Aminus hFrA (B t).localizedDomain hDlocal
    ((W t).comp (B t).originalInclusion) (hlocal t).2.2.1 hμlocal (B t).cylindricalCompletion

end FsFltz
