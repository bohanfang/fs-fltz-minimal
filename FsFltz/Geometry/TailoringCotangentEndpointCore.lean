import FsFltz.Geometry.TailoringCotangentEndpoint
import FsFltz.Analysis.TailoringCoreRadial

/-!
# Literal cotangent boundary formulas and the entire FLTZ link

Source: `geometric-part-fsf-proof.tex`, `prop:endpoint`, lines 1937–1959.
The radial normalization and witness factor are derived from the actual
strict completion map, and the whole positive-cone link is reached.

The same-potential theorem has explicit inputs: a strict native K=0
completion marking, the Legendre homeomorphisms for those selected potentials,
and their gradient agreement on the native positive homogeneous level. The
retained finite-input hitting-family theorem does not currently export these
inputs. No independent potential is selected here to replace them.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- The fixed Euclidean normalization in the literal cotangent boundary. -/
def cotangentNormalization (x : Cotangent n) : Cotangent n :=
  (x.1, (Real.sqrt (realSquaredNorm x.2))⁻¹ • x.2)

theorem cotangentNormalization_radialAction {x : Cotangent n} (hx : x ∈ cosphere) (r : ℝ) :
    cotangentNormalization (cotangentRadialAction r x) = x := by
  apply Prod.ext
  · rfl
  · change (Real.sqrt (realSquaredNorm (Real.exp r • x.2)))⁻¹ • (Real.exp r • x.2) = x.2
    rw [Geometry.realSquaredNorm_smul, show realSquaredNorm x.2 = 1 from hx,
      mul_one, Real.sqrt_sq (Real.exp_pos r).le, smul_smul,
      inv_mul_cancel₀ (Real.exp_pos r).ne', one_smul]

theorem radius_cotangentRadialAction {x : Cotangent n} (hx : x ∈ cosphere) (r : ℝ) :
    Real.sqrt (realSquaredNorm (cotangentRadialAction r x).2) = Real.exp r := by
  change Real.sqrt (realSquaredNorm (Real.exp r • x.2)) = _
  rw [Geometry.realSquaredNorm_smul, show realSquaredNorm x.2 = 1 from hx,
    mul_one, Real.sqrt_sq (Real.exp_pos r).le]

theorem CotangentPairData.boundaryCoordinates_mem_cosphere (E : CotangentPairData n)
    (x : E.pair.ambientDomain.domain.boundary.Point) : E.boundaryCoordinates x ∈ cosphere := by
  rw [← E.boundary_image]
  exact mem_range_self x

/-- The standard marking fixes its radial end formula at every real time. -/
theorem CotangentPairData.marking_end_all (E : CotangentPairData n)
    (x : E.pair.ambientDomain.domain.boundary.Point) (r : ℝ) :
    E.marking (E.pair.ambientCompletion.endMap (x, r)) =
      cotangentRadialAction r (E.boundaryCoordinates x) := by
  rw [E.pair.ambientCompletion.end_flow]
  exact E.pair.ambientCompletion.ambient.map_flow
    (cotangentCompletePrimitive n).toCompleteLiouvilleManifold E.marking E.primitive _ r

/-- The boundary representative of the same strict completion arrow is
the radial normalization of its value on the original boundary section. -/
theorem cotangentIdentification_boundary_normalization
    {P : WitnessedPair n} {E : CotangentPairData n}
    (J : CompletionIdentification P E.pair)
    (x : P.ambientDomain.domain.boundary.Point) :
    E.boundaryCoordinates (J.boundaryEquiv x) =
      cotangentNormalization (E.marking (J.ambientEquiv
        (P.ambientCompletion.inclusion.map (P.ambientDomain.domain.boundaryInclusion.map x)))) := by
  have he := congrArg E.marking (J.map_endMap x 0)
  rw [Completion.endMap_zero, zero_add, E.marking_end_all] at he
  rw [he, cotangentNormalization_radialAction (E.boundaryCoordinates_mem_cosphere _) _]

/-- The exact witness factor is the Euclidean momentum norm of the same
strict ambient map on the original boundary section. -/
theorem cotangentIdentification_shift_radius
    {P : WitnessedPair n} {E : CotangentPairData n}
    (J : CompletionIdentification P E.pair)
    (x : P.ambientDomain.domain.boundary.Point) :
    Real.exp (J.shift x) = Real.sqrt (realSquaredNorm
      (E.marking (J.ambientEquiv (P.ambientCompletion.inclusion.map
        (P.ambientDomain.domain.boundaryInclusion.map x)))).2) := by
  have he := congrArg E.marking (J.map_endMap x 0)
  rw [Completion.endMap_zero, zero_add, E.marking_end_all] at he
  rw [he, radius_cotangentRadialAction (E.boundaryCoordinates_mem_cosphere _) _]

/-- The endpoint's actual full embedded core is computed by normalizing
the same ambient map on the source's full embedded core. -/
theorem cotangentIdentification_embeddedCore_of_transport
    {P : WitnessedPair n} {E : CotangentPairData n}
    (J : CompletionIdentification P E.pair)
    (hcore : E.embeddedCore = E.boundaryCoordinates ''
      (J.boundaryEquiv '' P.embeddedCore)) :
    E.embeddedCore =
      (fun x => cotangentNormalization (E.marking (J.ambientEquiv
        (P.ambientCompletion.inclusion.map (P.ambientDomain.domain.boundaryInclusion.map x))))) ''
          P.embeddedCore := by
  rw [hcore, ← image_comp]
  apply image_congr
  intro x _
  exact cotangentIdentification_boundary_normalization J x

/-- Every literal positive-cone link point is represented on every positive
homogeneous potential level; no subset of the full link is omitted. -/
theorem IsStronglyCompatibleEndPotential.conic_level_projection_image
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φ u)
    (hΦzero : Φ 0 = 0) (hpositive : ∀ u ≠ 0, 0 < φ u)
    {A : ℝ} (hA : 0 < A) :
    tailoringRadialProjection φ ''
      (tailoringLegendreConic I φ ∩ {y : LGSpace n | φ y.1 = A}) = fltzLink I := by
  apply Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact tailoringRadialProjection_mem_link hy.1
  · intro z hz
    obtain ⟨hzunit, σ, hσ, hσzero, hθ, hp⟩ := hz
    have hpne : z.2 ≠ 0 := cotangent_ne_zero_of_mem_cosphere hzunit
    let u := Φ.symm z.2
    have hgrad : coordinateGradient φ u = z.2 := by
      rw [← hΦ]
      exact Φ.apply_symm_apply _
    have hune : u ≠ 0 := by
      intro hu
      apply hpne
      rw [← hgrad, ← hΦ, hu, hΦzero]
    let r := Real.sqrt (A / φ u)
    have hφpos := hpositive u hune
    have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hA hφpos)
    have hr2 : r ^ 2 = A / φ u := Real.sq_sqrt (div_pos hA hφpos).le
    have hscaledgrad : coordinateGradient φ (r • u) = r • z.2 := by
      rw [coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
        (fun v hv => (hφ.smooth v hv).differentiableAt (by simp)) hune hr, hgrad]
    refine ⟨(r • u, z.1), ⟨?_, ?_⟩, ?_⟩
    · refine ⟨?_, σ, hσ, hσzero, ?_, hθ⟩
      · rw [hscaledgrad]
        exact smul_ne_zero hr.ne' hpne
      · rw [hscaledgrad]
        exact I.smul_mem_of_mem_faceFan hσ hp hr.le
    · change φ (r • u) = A
      rw [hφ.homogeneous r hr u, hr2, div_mul_cancel₀ _ hφpos.ne']
    · apply Prod.ext
      · rfl
      · change (Real.sqrt (realSquaredNorm (coordinateGradient φ (r • u))))⁻¹ •
          coordinateGradient φ (r • u) = z.2
        rw [hscaledgrad, FsFltz.realSquaredNorm_smul,
          show realSquaredNorm z.2 = 1 from hzunit, mul_one, Real.sqrt_sq hr.le,
          smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The native full-core equality supplies the literal endpoint. The strict
map is the same map used in both boundary normalization and witness transport;
the retained ribbon has identity map and scale one. -/
theorem exists_literal_cotangentEndpoint_of_nativeCore
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    (ΦEnd : RealSpace n ≃ₜ RealSpace n)
    (hΦEnd : ∀ u, ΦEnd u = coordinateGradient φEnd u) (hΦEndzero : ΦEnd 0 = 0)
    (hpositive : ∀ u ≠ 0, 0 < φEnd u) {A : ℝ} (hA : 0 < A)
    (P : WitnessedPair n) (i : P.ambientDomain.domain.boundary.Point → LGSpace n)
    (f : P.ambientManifold.SmoothEquiv (cotangentManifold n))
    (hf : P.ambientManifold.pullback (cotangentManifold n) f (lambdaCanForm n) =
      P.ambientCompletion.ambient.primitive)
    (hboundary : ∀ x, f (P.ambientCompletion.inclusion.map
      (P.ambientDomain.domain.boundaryInclusion.map x)) =
        ((i x).2, coordinateGradient φEnd (i x).1))
    (hcore : i '' P.embeddedCore = tailoringLegendreConic I φEnd ∩ range i)
    (hlevel : range i = {y : LGSpace n | φEnd y.1 = A}) :
    ∃ E : CotangentPairData n, ∃ J : CompletionIdentification P E.pair,
      J.ambientEquiv.trans E.marking = f ∧
      E.pair.ribbonDomain = P.ribbonDomain ∧
      HEq E.pair.ribbonCompletion P.ribbonCompletion ∧
      HEq J.ribbonEquiv.map (id : P.ribbonDomain.domain.extension.Point →
        P.ribbonDomain.domain.extension.Point) ∧ J.scale = 1 ∧
      (∀ x, E.boundaryCoordinates (J.boundaryEquiv x) = tailoringRadialProjection φEnd (i x)) ∧
      (∀ x, E.pair.witness (J.boundaryEquiv x) =
        Real.sqrt (realSquaredNorm (coordinateGradient φEnd (i x).1)) * P.witness x) ∧
      E.embeddedCore = fltzLink I := by
  obtain ⟨E, J, hmap, hdomain, hcompletion, hribbon, hscale, hwitness, htransport⟩ :=
    exists_cotangentEndpoint_of_strictMarking P f hf
  have hmapPoint (x : P.ambientDomain.domain.boundary.Point) :
      E.marking (J.ambientEquiv (P.ambientCompletion.inclusion.map
        (P.ambientDomain.domain.boundaryInclusion.map x))) =
          ((i x).2, coordinateGradient φEnd (i x).1) := by
    exact (congrArg (fun g => g (P.ambientCompletion.inclusion.map
      (P.ambientDomain.domain.boundaryInclusion.map x))) hmap).trans (hboundary x)
  have hb (x : P.ambientDomain.domain.boundary.Point) :
      E.boundaryCoordinates (J.boundaryEquiv x) = tailoringRadialProjection φEnd (i x) := by
    rw [cotangentIdentification_boundary_normalization J x, hmapPoint]
    rfl
  refine ⟨E, J, hmap, hdomain, hcompletion, hribbon, hscale, hb, ?_, ?_⟩
  · intro x
    rw [hwitness, cotangentIdentification_shift_radius J x, hmapPoint]
  · rw [cotangentIdentification_embeddedCore_of_transport J htransport]
    calc
      _ = tailoringRadialProjection φEnd '' (i '' P.embeddedCore) := by
        rw [← image_comp]
        apply image_congr
        intro x _
        rw [hmapPoint]
        rfl
      _ = tailoringRadialProjection φEnd ''
          (tailoringLegendreConic I φEnd ∩ {y : LGSpace n | φEnd y.1 = A}) := by
        rw [hcore, hlevel]
      _ = fltzLink I := hstrong.conic_level_projection_image ΦEnd hΦEnd hΦEndzero hpositive hA

/-- A marking into the native logarithmic ambient and the Legendre map of
that very same potential construct the strict endpoint arrow. No new
potential is selected. The explicit native core and level equations then
give the entire FLTZ link and the source's prescribed witness factor. -/
theorem exists_literal_cotangentEndpoint_of_samePotential
    {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    (ΦEnd : RealSpace n ≃ₜ RealSpace n)
    (hΦEnd : ∀ u, ΦEnd u = coordinateGradient φEnd u) (hΦEndzero : ΦEnd 0 = 0)
    (hpositive : ∀ u ≠ 0, 0 < φEnd u) {A : ℝ} (hA : 0 < A)
    (hφ : ContDiff ℝ ∞ φ) (Φ : RealSpace n ≃ₜ RealSpace n)
    (hΦ : ∀ u, Φ u = coordinateGradient φ u) (hΦinv : ContDiff ℝ ∞ Φ.symm)
    (P : WitnessedPair n) (i : P.ambientDomain.domain.boundary.Point → LGSpace n)
    (q : P.ambientManifold.SmoothEquiv (lgManifold n))
    (hq : P.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
      P.ambientCompletion.ambient.primitive)
    (hboundary : ∀ x, q (P.ambientCompletion.inclusion.map
      (P.ambientDomain.domain.boundaryInclusion.map x)) = i x)
    (hgradient : ∀ x, coordinateGradient φ (i x).1 = coordinateGradient φEnd (i x).1)
    (hcore : i '' P.embeddedCore = tailoringLegendreConic I φEnd ∩ range i)
    (hlevel : range i = {y : LGSpace n | φEnd y.1 = A}) :
    ∃ E : CotangentPairData n, ∃ J : CompletionIdentification P E.pair,
      (∀ y, E.marking (J.ambientEquiv y) = ((q y).2, coordinateGradient φ (q y).1)) ∧
      E.pair.ribbonDomain = P.ribbonDomain ∧
      HEq E.pair.ribbonCompletion P.ribbonCompletion ∧
      HEq J.ribbonEquiv.map (id : P.ribbonDomain.domain.extension.Point →
        P.ribbonDomain.domain.extension.Point) ∧ J.scale = 1 ∧
      (∀ x, E.boundaryCoordinates (J.boundaryEquiv x) = tailoringRadialProjection φEnd (i x)) ∧
      (∀ x, E.pair.witness (J.boundaryEquiv x) =
        Real.sqrt (realSquaredNorm (coordinateGradient φEnd (i x).1)) * P.witness x) ∧
      E.embeddedCore = fltzLink I := by
  have hΦsmooth : ContDiff ℝ ∞ Φ := by
    rw [show (Φ : RealSpace n → RealSpace n) = coordinateGradient φ from funext hΦ]
    exact contDiff_coordinateGradient hφ
  let L := legendreDiffeomorph Φ hΦsmooth hΦinv
  let f := q.trans L
  have hL : (lgManifold n).pullback (cotangentManifold n) L (lambdaCanForm n) =
      lambdaPotentialForm φ := by
    have hfun : (L : LGSpace n → Cotangent n) = legendreMap (coordinateGradient φ) := by
      funext y
      simp [L, hΦ, legendreMap]
    rw [hfun]
    exact pullback_lambdaCanForm_legendreMap hφ
  have hf : P.ambientManifold.pullback (cotangentManifold n) f (lambdaCanForm n) =
      P.ambientCompletion.ambient.primitive := by
    change P.ambientManifold.pullback (cotangentManifold n) (L ∘ q) (lambdaCanForm n) = _
    rw [P.ambientManifold.pullback_comp (lgManifold n) (cotangentManifold n)
      (q.contMDiff.mdifferentiable (by simp)) (L.contMDiff.mdifferentiable (by simp)), hL, hq]
  have hfb (x : P.ambientDomain.domain.boundary.Point) :
      f (P.ambientCompletion.inclusion.map (P.ambientDomain.domain.boundaryInclusion.map x)) =
        ((i x).2, coordinateGradient φEnd (i x).1) := by
    change L (q _) = _
    rw [hboundary]
    simp [L, hΦ, hgradient]
  obtain ⟨E, J, hmap, hdomain, hcompletion, hribbon, hscale, hb, hw, hc⟩ :=
    exists_literal_cotangentEndpoint_of_nativeCore hstrong ΦEnd hΦEnd hΦEndzero hpositive hA
      P i f hf hfb hcore hlevel
  refine ⟨E, J, ?_, hdomain, hcompletion, hribbon, hscale, hb, hw, hc⟩
  intro y
  have hm := congrArg (fun g => g y) hmap
  exact hm.trans (by simp [f, L, hΦ])

end FsFltz
