import FsFltz.Geometry.EmbeddedCarrierCompactMap
import FsFltz.Geometry.NativeCompactMapCompletion
import FsFltz.Geometry.PotentialFiberMarking
import FsFltz.Geometry.PotentialAmbientPath

/-!
# Full-fiber markings for the actual retained holomorphic ribbon

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1049,
and assembly, lines 2127–2158. The whole native regular fiber, its actual
moving potential primitive and its complete flow construct a marking on
every supplied retained ribbon completion. The result is pointwise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

/-- Finite geometric hypotheses construct actual markings from every
retained ribbon completion onto the whole fiber, with the literal moving
potential primitive and the same compact inclusion square. -/
theorem ToricInput.coefficientPath_potentialPath_exists_uniform_retainedRibbon_markings
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
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
      let ψ := potentialPath (fun u => realSquaredNorm u / 2) φ s
      ∀ D : LiouvilleDomain (2 * n - 2), D.domain.carrier.Nonempty →
      ∀ jD : D.domain.extension.SmoothEmbedding (lgManifold n),
        jD.map '' D.domain.carrier =
          {y | W (I.alongCoefficientPath s) y = (Real.exp β : ℂ) ∧ ψ y.1 ≤ A} →
      (∀ x ∈ D.domain.carrier,
        D.liouville.primitive x = D.domain.extension.pullback (lgManifold n) jD.map
          (lambdaPotentialForm ψ) x) →
      ∀ C : Completion D,
        ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
          (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm ψ)))
          (i : D.domain.Point → N.Point),
          range j.map = {y | W (I.alongCoefficientPath s) y = (Real.exp β : ℂ)} ∧
          (∀ x, j.map (i x) = jD.map x.val) ∧
          ∃ q : InclusionMarking C P.toCompleteLiouvilleManifold i,
            ∀ b r, q.equiv (C.endMap (b, r)) = P.completeFlow.flow r
              (i ⟨D.domain.boundaryInclusion.map b,
                D.domain.boundaryInclusion_mem_carrier b⟩) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hφE := hφ.comp e.contDiff
  have hEndE := hEnd1.comp e.contDiff
  have hEndsE : ∀ u ≠ 0, ContDiffAt ℝ ∞ (φEnd ∘ e) u := by
    intro u hu
    apply (hEnd (e u) (by
      intro hz
      apply hu
      apply e.injective
      simpa only [map_zero] using hz)).comp u e.contDiff.contDiffAt
  have hhomE : ∀ r : ℝ, 0 < r → ∀ u, (φEnd ∘ e) (r • u) = r ^ 2 * (φEnd ∘ e) u := by
    intro r hr u
    simpa only [Function.comp_apply, map_smul] using hhom r hr (e u)
  have hendE : ∀ u, L ≤ ‖u‖ → (φ ∘ e) u = (φEnd ∘ e) u := by
    intro u hu
    exact hend (e u) hu
  obtain ⟨F, hF, Be, hBe, hout⟩ := I.coefficientPath_potentialPath_intrinsic_fiber_outward
    hφE hEndE hEndsE hhomE hc hlower hupper hL hendE 0
  obtain ⟨B, _hB, hregular⟩ := I.coefficientPath_a_pos_of_large_value
  refine ⟨F, hF, max Be B, hBe.trans_le (le_max_left _ _), ?_⟩
  intro β hβ s hs A hA ψ D hD jD hjD hμ C
  have hfar : B < Real.exp β := by
    have hBβ : B ≤ β := (le_max_right _ _).trans hβ
    linarith [Real.add_one_le_exp β]
  have ha : ∀ y, W (I.alongCoefficientPath s) y = (Real.exp β : ℂ) →
      0 < a (I.alongCoefficientPath s) y := by
    intro y hy
    apply hregular s hs y
    rw [hy, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos β)]
    exact hfar
  have hψ := potentialPath_native_contDiff hφ s
  have hψEnd1 := potentialPath_native_end_contDiff hEnd1 s
  have hψEnd := potentialPath_native_end_contDiffAt hEnd s
  have hψhom := potentialPath_native_end_homogeneous hhom s
  have hψc := lt_min zero_lt_one hc
  have hψU : 0 < max 1 U := zero_lt_one.trans_le (le_max_left _ _)
  have hψlower := potentialPath_native_hessian_lowerBound hφ hlower hs
  have hψupper := potentialPath_native_hessian_upperBound hφ hupper hs
  have hψend := potentialPath_native_eq_end hend s
  obtain ⟨N, j, himage, _hsymp⟩ := exists_potential_W_level_symplecticEmbedding
    hψ hψc hψU hψlower hψupper (I.alongCoefficientPath s) (Real.exp β : ℂ) ha
  let P := potential_W_levelCompletePrimitive hψ hψEnd1 hψEnd hψhom hψc hψU
    hψlower hψupper hL hψend (I.alongCoefficientPath s) (Real.exp β : ℂ) ha j himage
  have hψeq : potentialPath (fun u => ‖u‖ ^ 2 / 2) (φ ∘ e) s ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm = ψ := by
    funext u
    change (1 - s) * (‖e.symm u‖ ^ 2 / 2) + s * φ (e (e.symm u)) =
      (1 - s) * (realSquaredNorm u / 2) + s * φ u
    rw [e.apply_symm_apply]
    congr 2
    simp [e, EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hpos (x : N.Point) (hx : A ≤ ψ (j.map x).1) :
      0 < N.scalarDerivative (fun y => ψ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm ψ)) x) := by
    have hval : W (I.alongCoefficientPath s) (j.map x) = (Real.exp β : ℂ) := by
      have hy : j.map x ∈ range j.map := ⟨x, rfl⟩
      rwa [himage] at hy
    have h := ((hout β ((le_max_left _ _).trans hβ)).2 s hs s hs (2 * n - 2) N j x
      (potential_W_levelEmbedding_tangent_range (I.alongCoefficientPath s)
        (Real.exp β : ℂ) ha j himage x)
      (by simpa only [hψeq] using hA.trans hx)
      (by rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos β)])).2
    change 0 < N.scalarDerivative
      ((fun y => (potentialPath (fun u => ‖u‖ ^ 2 / 2) (φ ∘ e) s ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) y.1) ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map
        (lambdaPotentialForm (potentialPath (fun u => ‖u‖ ^ 2 / 2) (φ ∘ e) s ∘
          (EuclideanSpace.equiv (Fin n) ℝ).symm))) x) at h
    rw [hψeq] at h
    exact h
  let E := potential_W_levelOutwardDomain hψ hψEnd1 hψEnd hψhom hψc hψU hψlower hψupper
    hL hψend (I.alongCoefficientPath s) (Real.exp β : ℂ) ha j himage A hpos
  have hEimage := potential_W_levelOutwardDomain_image hψ hψEnd1 hψEnd hψhom hψc hψU
    hψlower hψupper hL hψend (I.alongCoefficientPath s) (Real.exp β : ℂ) ha j himage A hpos
  obtain ⟨h, hsquare, _hinverse⟩ := D.domain.exists_compactDiffeomorph_of_embeddedCarrier
    E.domain (lgManifold n) hD jD j (hjD.trans hEimage.symm)
  have hp (x) (hx : x ∈ D.domain.carrier) :
      D.domain.extension.pullback E.domain.extension h.map E.liouville.primitive x =
        D.liouville.primitive x := by
    change D.domain.extension.pullback N h.map
      (N.pullback (lgManifold n) j.map (lambdaPotentialForm ψ)) x = _
    erw [h.pullback_of_embeddedCarrier (lgManifold n) jD j hsquare (lambdaPotentialForm ψ) x hx]
    exact (hμ x hx).symm
  let C' := potential_W_levelOutwardCompletion hψ hψEnd1 hψEnd hψhom hψc hψU hψlower hψupper
    hL hψend (I.alongCoefficientPath s) (Real.exp β : ℂ) ha j himage A hpos
  obtain ⟨eqv, _b, he, hecompact, _heboundary, _heend⟩ :=
    C.exists_strictEquiv_of_compactDiffeomorph C' h hp
  let q : InclusionMarking C P.toCompleteLiouvilleManifold (fun x => h.map x.val) :=
    { equiv := eqv
      primitive := he
      inclusion := fun x => hecompact x.val x.property
      flow_induced := fun b r => by
        rw [C.end_flow, C.ambient.map_flow P.toCompleteLiouvilleManifold eqv he] }
  refine ⟨N, j, P, (fun x => h.map x.val), himage,
    (fun x => hsquare x.val x.property), q, ?_⟩
  intro b r
  rw [q.flow_induced, q.inclusion
    ⟨D.domain.boundaryInclusion.map b, D.domain.boundaryInclusion_mem_carrier b⟩]
  rfl

end FsFltz.Geometry
