import FsFltz.Geometry.IntervalMaslovFamilyPullback
import FsFltz.Geometry.IntrinsicNativeCompletionOriginalSectionEndpoints

/-!
# A preselected original section on a chosen completed deformation

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
The original compatible field and canonical-square section are fixed on an
independent completed ambient. Genuine source-local open extension laws
reconstruct their family. A supplied geometric comparison with the chosen
completed deformation then transports that very section, constructs all slice
representatives, and derives the endpoint restrictions required to grade the
same deformation. Every tensor slot and actual completion presentation remain
in the equations.

The interval comparison and its real smooth extension are explicit inputs.
Constructing them from a raw untrivialized original completed bundle remains
pending. This conditional foundation constructs neither the geometric chain
nor the prescribed endpoint datum in `thm:target`, lines 385–413.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology

namespace FsFltz.Geometry.PairDeformation

variable {n : ℕ}

/-- The comparison of an actual slice uses the inverse of its specified
completion presentation, followed by the independent original comparison. -/
def preselectedCompletionSliceComparison (Q : PairDeformation n)
    (N : SmoothManifold (2 * n)) (e : Parameter → Q.source.ambientManifold.SmoothEquiv N)
    (s : Parameter) : (Q.pair s).ambientManifold.SmoothEquiv N :=
  (Q.ambientCompletionPresentation s).equiv.symm.trans (e s)

/-- The derived slice map preserves the original primitive. No primitive
or derivative equation for the slice map is assumed independently. -/
theorem preselectedCompletionSliceComparison_primitive (Q : PairDeformation n)
    (N : SmoothManifold (2 * n)) (lamN : ℝ → N.Form 1)
    (e : Parameter → Q.source.ambientManifold.SmoothEquiv N)
    (hp : ∀ s : Parameter, Q.source.ambientManifold.pullback N (e s) (lamN s.val) =
      Q.completedPrimitive s) (s : Parameter) :
    (Q.pair s).ambientManifold.pullback N (Q.preselectedCompletionSliceComparison N e s)
      (lamN s.val) = (Q.pair s).ambientCompletion.ambient.primitive := by
  unfold preselectedCompletionSliceComparison
  change (Q.pair s).ambientManifold.pullback N
    ((e s) ∘ (Q.ambientCompletionPresentation s).equiv.symm) (lamN s.val) = _
  rw [(Q.pair s).ambientManifold.pullback_comp Q.source.ambientManifold N
    ((Q.ambientCompletionPresentation s).equiv.symm.mdifferentiable (by simp))
    ((e s).mdifferentiable (by simp)), hp s]
  exact Q.source.ambientManifold.pullback_symm_pullback (Q.pair s).ambientManifold
    (Q.ambientCompletionPresentation s).equiv (Q.pair s).ambientCompletion.ambient.primitive

/-- Exterior naturality derives the actual symplectic equation of the same
slice comparison from its primitive equation. -/
theorem preselectedCompletionSliceComparison_symplectic (Q : PairDeformation n)
    (N : SmoothManifold (2 * n)) (lamN : ℝ → N.Form 1)
    (hlamN : ∀ s : Parameter, N.IsSmoothForm (lamN s.val))
    (e : Parameter → Q.source.ambientManifold.SmoothEquiv N)
    (hp : ∀ s : Parameter, Q.source.ambientManifold.pullback N (e s) (lamN s.val) =
      Q.completedPrimitive s) (s : Parameter) :
    (Q.pair s).ambientManifold.pullback N (Q.preselectedCompletionSliceComparison N e s)
      (N.exteriorDerivative (lamN s.val)) = (Q.pair s).ambientSymplecticForm := by
  exact ((Q.pair s).ambientManifold.exteriorDerivative_pullback N
    (Q.preselectedCompletionSliceComparison N e s).toContMDiffMap
    (lamN s.val) (hlamN s)).symm.trans
      (congrArg (Q.pair s).ambientManifold.exteriorDerivative
        (Q.preselectedCompletionSliceComparison_primitive N lamN e hp s))

/-- The original canonical-square section is fixed before the deformation
and comparison are supplied. Local source germs reconstruct its full family;
the actual comparison then constructs every slice representative and derives
the endpoint restrictions. The same pullback section retains genuine local
complex and scalar extensions and grades the literal chosen deformation.

The geometry-only interval comparison, its smooth real extension, and its
primitive equation remain inputs. They are the exact outstanding bridge from
an arbitrary original untrivialized completed bundle. -/
theorem exists_grading_with_endpoints_of_preselectedSection
    (N : SmoothManifold (2 * n)) (lamN : ℝ → N.Form 1)
    (hlamN : ∀ s : Parameter, N.IsSmoothForm (lamN s.val))
    (J : ℝ → AlmostComplexField N)
    (hcompatible : ∀ t ∈ parameterInterval,
      IsCompatibleAlmostComplex N (N.exteriorDerivative (lamN t)) (J t))
    (hJ : HasLocalSmoothIntervalComplexExtensions N J)
    (σ : (p : Parameter × N.Point) → CanonicalTensorSquare (J p.1.val p.2))
    (hnσ : ∀ p, σ p ≠ 0)
    (hσ : HasLocalSmoothIntervalTensorCoefficients N J σ)
    (Q : PairDeformation n)
    (e : Parameter → Q.source.ambientManifold.SmoothEquiv N)
    (he : Q.source.ambientManifold.IsSmoothIntervalMapFamily N (fun t => e t))
    (hp : ∀ s : Parameter, Q.source.ambientManifold.pullback N (e s) (lamN s.val) =
      Q.completedPrimitive s) :
    ∃ f : MaslovFamily N (fun t => N.exteriorDerivative (lamN t)),
      (∀ s : Parameter, f.J s.val = J s.val) ∧
      (∀ p : Parameter × N.Point, f.tensor p.1.val p.2 =
        (canonicalSquareMap (J p.1.val p.2) (σ p)).val) ∧
      HasLocalSmoothIntervalComplexExtensions Q.source.ambientManifold
        (intervalPullbackAlmostComplex Q.source.ambientManifold N e f.J) ∧
      ∃ τ : (p : Parameter × Q.source.ambientManifold.Point) →
          CanonicalTensorSquare
            (intervalPullbackAlmostComplex Q.source.ambientManifold N e f.J p.1.val p.2),
        (∀ p, τ p ≠ 0) ∧
        HasLocalSmoothIntervalTensorCoefficients Q.source.ambientManifold
          (intervalPullbackAlmostComplex Q.source.ambientManifold N e f.J) τ ∧
        (∀ (s : Parameter) x,
          (canonicalSquareMap
            (intervalPullbackAlmostComplex Q.source.ambientManifold N e f.J s.val x)
            (τ (s, x))).val = pullbackSquaredTensor Q.source.ambientManifold N (e s)
              (fun y => (canonicalSquareMap (J s.val y) (σ (s, y))).val) x) ∧
      ∃ endpoints : ∀ s, (Q.pair s).Maslov,
        (∀ s, (endpoints s).J = pullbackAlmostComplex (Q.pair s).ambientManifold N
          (Q.preselectedCompletionSliceComparison N e s) (J s.val)) ∧
        (∀ s, (endpoints s).tensor = pullbackSquaredTensor (Q.pair s).ambientManifold N
          (Q.preselectedCompletionSliceComparison N e s)
          (fun y => (canonicalSquareMap (J s.val y) (σ (s, y))).val)) ∧
      ∃ g : GradedPairDeformation Q (endpoints parameterZero) (endpoints parameterOne),
        ∃ lift : NativeGradedComparisonStep (.deformation Q)
            (endpoints parameterZero) (endpoints parameterOne),
          lift = .deformation g ∧
          (∀ s : Parameter, g.family.J s.val =
            pullbackAlmostComplex Q.source.ambientManifold N (e s) (J s.val)) ∧
          (∀ s : Parameter, g.family.tensor s.val =
            pullbackSquaredTensor Q.source.ambientManifold N (e s)
              (fun y => (canonicalSquareMap (J s.val y) (σ (s, y))).val)) ∧
          ∀ (s : Parameter) x,
            g.family.tensor s.val x = (canonicalSquareMap
              (intervalPullbackAlmostComplex Q.source.ambientManifold N e f.J s.val x)
              (τ (s, x))).val := by
  obtain ⟨f, hfJ, hfT⟩ := exists_maslovFamily_of_localExtensions J hcompatible hJ σ hnσ hσ
  have hTf (s : Parameter) : f.tensor s.val =
      (fun y => (canonicalSquareMap (J s.val y) (σ (s, y))).val) :=
    funext (fun y => hfT (s, y))
  have hform (s : Parameter) : Q.source.ambientManifold.pullback N (e s)
      (N.exteriorDerivative (lamN s.val)) =
        Q.source.ambientManifold.exteriorDerivative (Q.completedPrimitive s) := by
    exact (Q.source.ambientManifold.exteriorDerivative_pullback N (e s).toContMDiffMap
      (lamN s.val) (hlamN s)).symm.trans
        (congrArg Q.source.ambientManifold.exteriorDerivative (hp s))
  let endpoints : ∀ s, (Q.pair s).Maslov := fun s =>
    (f.representative s).pullbackTo (Q.preselectedCompletionSliceComparison N e s)
      (Q.preselectedCompletionSliceComparison_symplectic N lamN hlamN e hp s)
  have hJE (s : Parameter) : (endpoints s).J =
      pullbackAlmostComplex (Q.pair s).ambientManifold N
        (Q.preselectedCompletionSliceComparison N e s) (J s.val) := by
    change pullbackAlmostComplex _ _ _ (f.J s.val) = _
    rw [hfJ s]
  have hTE (s : Parameter) : (endpoints s).tensor =
      pullbackSquaredTensor (Q.pair s).ambientManifold N
        (Q.preselectedCompletionSliceComparison N e s)
        (fun y => (canonicalSquareMap (J s.val y) (σ (s, y))).val) := by
    change pullbackSquaredTensor _ _ _ (f.tensor s.val) = _
    rw [hTf s]
  have hJendpoint (s : Parameter) :
      pullbackAlmostComplex Q.source.ambientManifold N (e s) (f.J s.val) =
      pullbackAlmostComplex Q.source.ambientManifold (Q.pair s).ambientManifold
        (Q.ambientCompletionPresentation s).equiv (endpoints s).J := by
    change _ = pullbackAlmostComplex _ _ _
      (pullbackAlmostComplex _ _
        ((Q.ambientCompletionPresentation s).equiv.symm.trans (e s)) (f.J s.val))
    have hmap : (Q.ambientCompletionPresentation s).equiv.trans
        ((Q.ambientCompletionPresentation s).equiv.symm.trans (e s)) = e s :=
      Diffeomorph.ext (fun x => congrArg (e s)
        ((Q.ambientCompletionPresentation s).equiv.symm_apply_apply x))
    rw [← pullbackAlmostComplex_trans, hmap]
  have hTendpoint (s : Parameter) :
      pullbackSquaredTensor Q.source.ambientManifold N (e s) (f.tensor s.val) =
      pullbackSquaredTensor Q.source.ambientManifold (Q.pair s).ambientManifold
        (Q.ambientCompletionPresentation s).equiv (endpoints s).tensor := by
    change _ = pullbackSquaredTensor _ _ _
      (pullbackSquaredTensor _ _
        ((Q.ambientCompletionPresentation s).equiv.symm.trans (e s)) (f.tensor s.val))
    have hmap : (Q.ambientCompletionPresentation s).equiv.trans
        ((Q.ambientCompletionPresentation s).equiv.symm.trans (e s)) = e s :=
      Diffeomorph.ext (fun x => congrArg (e s)
        ((Q.ambientCompletionPresentation s).equiv.symm_apply_apply x))
    rw [← pullbackSquaredTensor_trans, hmap]
  obtain ⟨g, hgJ, hgT⟩ := GradedPairDeformation.exists_of_intervalPullback N f e he
    Q.completedSymplecticExtension Q.completedSymplecticExtension_apply
    (fun s => by rw [Q.completedSymplecticExtension_apply]; exact hform s)
    (hJendpoint parameterZero) (hJendpoint parameterOne)
    (hTendpoint parameterZero) (hTendpoint parameterOne)
  refine ⟨f, hfJ, hfT, f.localSmoothComplexExtensions_intervalPullback e he,
    f.intervalPullbackTensorSection e, f.intervalPullbackTensorSection_ne_zero e,
    f.localSmoothTensorCoefficients_intervalPullback e he, ?_, endpoints, hJE, hTE,
    g, .deformation g, rfl, ?_, ?_, ?_⟩
  · intro s x
    exact (f.canonicalSquareMap_intervalPullbackTensorSection e (s, x)).trans
      (congrArg (fun T => pullbackSquaredTensor Q.source.ambientManifold N (e s) T x) (hTf s))
  · intro s
    rw [hgJ s, hfJ s]
  · intro s
    rw [hgT s, hTf s]
  · intro s x
    exact (congrFun (hgT s) x).trans
      (f.canonicalSquareMap_intervalPullbackTensorSection e (s, x)).symm

end FsFltz.Geometry.PairDeformation
