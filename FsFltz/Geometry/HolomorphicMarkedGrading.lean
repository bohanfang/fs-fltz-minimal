import FsFltz.Geometry.PotentialLogarithmicGrading
import FsFltz.Geometry.PotentialTailoringMarkedChain
import FsFltz.Geometry.LocalGermMaslovFamilyPullback
import FsFltz.Geometry.PairDeformationMaslovFamily

/-!
# Grading on the retained holomorphic completed deformation

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1993–1998.
The given smooth inclusion markings transport the actual fixed logarithmic
fields and tensor through this very completed family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Pull back the native representative through the actual marking of this slice. -/
def FullAmbientInclusionMarkingFamily.maslovAt {n : ℕ}
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {α : ℝ → (lgManifold n).Form 1}
    (M : FullAmbientInclusionMarkingFamily Q J (fun t => α t.val))
    (hα : ∀ t : Parameter, (lgManifold n).IsSmoothForm (α t.val))
    (f : MaslovFamily (lgManifold n) (fun t => (lgManifold n).exteriorDerivative (α t)))
    (t : Parameter) : (Q.pair t).Maslov :=
  pullbackPrimitiveMaslovRepresentative (Q.pair t).ambientManifold (lgManifold n)
    (Q.pair t).ambientCompletion.ambient.primitive (α t.val) (M.marking t).equiv
    (hα t) (M.marking t).primitive (f.representative t)

/-- Actual smooth full-ambient markings pull a native family back to the
same completed deformation, retaining exact pointwise endpoint representatives. -/
theorem FullAmbientInclusionMarkingFamily.exists_grading {n : ℕ}
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {α : ℝ → (lgManifold n).Form 1}
    (M : FullAmbientInclusionMarkingFamily Q J (fun t => α t.val))
    (hα : ∀ t : Parameter, (lgManifold n).IsSmoothForm (α t.val))
    (f : MaslovFamily (lgManifold n) (fun t => (lgManifold n).exteriorDerivative (α t))) :
    Nonempty (GradedPairDeformation Q (M.maslovAt hα f parameterZero)
      (M.maslovAt hα f parameterOne)) := by
  let e : Parameter → Q.source.ambientManifold.SmoothEquiv (lgManifold n) :=
    fun t => (Q.ambientCompletionPresentation t).equiv.trans (M.marking t).equiv
  have hprimitive (t : Parameter) :
      Q.source.ambientManifold.pullback (lgManifold n) (e t) (α t.val) =
        Q.completedPrimitive t := by
    change Q.source.ambientManifold.pullback (lgManifold n)
      ((M.marking t).equiv ∘ (Q.ambientCompletionPresentation t).equiv) _ = _
    have hp : (Q.pair t).ambientManifold.pullback (lgManifold n) (M.marking t).equiv
        (α t.val) = (Q.pair t).ambientCompletion.ambient.primitive := (M.marking t).primitive
    rw [Q.source.ambientManifold.pullback_comp (Q.pair t).ambientManifold (lgManifold n)
      ((Q.ambientCompletionPresentation t).equiv.mdifferentiable (by simp))
      ((M.marking t).equiv.mdifferentiable (by simp)), hp]
    rfl
  have hform (t : Parameter) :
      Q.source.ambientManifold.pullback (lgManifold n) (e t)
        ((lgManifold n).exteriorDerivative (α t.val)) = Q.completedSymplecticExtension t.val := by
    exact (Q.source.ambientManifold.exteriorDerivative_pullback (lgManifold n)
      (e t).toContMDiffMap _ (hα t)).symm.trans
        ((congrArg Q.source.ambientManifold.exteriorDerivative (hprimitive t)).trans
          (Q.completedSymplecticExtension_apply t).symm)
  obtain ⟨g, _, _⟩ := GradedPairDeformation.exists_of_localGermPullback
    (source := M.maslovAt hα f parameterZero) (target := M.maslovAt hα f parameterOne)
    (lgManifold n) f e M.forward_smooth
    Q.completedSymplecticExtension Q.completedSymplecticExtension_apply hform
    (pullbackAlmostComplex_trans _ _ _ (Q.ambientCompletionPresentation parameterZero).equiv
      (M.marking parameterZero).equiv _)
    (pullbackAlmostComplex_trans _ _ _ (Q.ambientCompletionPresentation parameterOne).equiv
      (M.marking parameterOne).equiv _)
    (pullbackSquaredTensor_trans _ _ _ (Q.ambientCompletionPresentation parameterZero).equiv
      (M.marking parameterZero).equiv _)
    (pullbackSquaredTensor_trans _ _ _ (Q.ambientCompletionPresentation parameterOne).equiv
      (M.marking parameterOne).equiv _)
  exact ⟨g⟩

/-- The pullback of the literal logarithmic tensor has exactly the
prescribed marked values, independently of the potential primitive. -/
theorem FullAmbientInclusionMarkingFamily.maslovAt_prescribed {n : ℕ}
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {α : ℝ → (lgManifold n).Form 1}
    (M : FullAmbientInclusionMarkingFamily Q J (fun t => α t.val))
    (hα : ∀ t : Parameter, (lgManifold n).IsSmoothForm (α t.val))
    (f : MaslovFamily (lgManifold n) (fun t => (lgManifold n).exteriorDerivative (α t)))
    (t : Parameter) (hf : f.tensor t.val = logarithmicSquaredVolumeTensor n) :
    IsLogarithmicGrading (M.marking t).equiv (M.maslovAt hα f t) := by
  intro x v
  change f.tensor t.val ((M.marking t).equiv x)
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      (M.marking t).equiv x (v i)) = _
  rw [hf, logarithmicSquaredVolumeTensor_apply]
  apply congrArg coordinateSquaredVolumeValue
  funext i
  exact (logarithmicTangentCoordinates_naturality _ _ x (v i)).symm

/-- The actual retained holomorphic deformation carries the prescribed
logarithmic tensor at both ends. No Maslov family is an input. -/
theorem FullAmbientInclusionMarkingFamily.exists_logarithmic_potential_grading {n : ℕ}
    {I : ToricInput n} {φ : RealSpace n → ℝ} {K : ℝ}
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    (M : FullAmbientInclusionMarkingFamily Q J (fun t =>
      (lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
        (W (I.alongCoefficientPath t.val)) K))
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hK : 0 ≤ K) :
    ∃ s : Q.source.Maslov,
    ∃ u : Q.target.Maslov,
      IsLogarithmicGrading (M.marking parameterZero).equiv s ∧
      IsLogarithmicGrading (M.marking parameterOne).equiv u ∧
      Nonempty (GradedPairDeformation Q s u) := by
  let ψ := potentialPath (fun u => realSquaredNorm u / 2) φ
  have hψ (t : ℝ) : ContDiff ℝ ∞ (ψ t) := by
    exact (((contDiff_realSquaredNorm.div_const 2).const_smul (1 - t)).add
      (hφ.const_smul t))
  have hl (t : ℝ) (ht : t ∈ parameterInterval) (u v : EuclideanSpace ℝ (Fin n)) :
      min 1 c * ‖v‖ ^ 2 ≤ inner ℝ
        (fderiv ℝ (gradient (ψ t ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v := by
    have he : ψ t ∘ EuclideanSpace.equiv (Fin n) ℝ =
        potentialPath (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 / 2)
          (φ ∘ EuclideanSpace.equiv (Fin n) ℝ) t := by
      funext z
      simp [ψ, potentialPath, realSquaredNorm, EuclideanSpace.norm_sq_eq]
    rw [he]
    exact hessian_potentialPath_lowerBound ((contDiff_id.norm_sq ℝ).div_const 2)
      (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
      (fun x w => by simp [hessian_half_norm_sq]) hlower ht u v
  let f := logarithmicPotentialMaslovFamily (fun t => I.alongCoefficientPath t) ψ
    (lt_min zero_lt_one hc) (fun t _ => hψ t) hl
    hK
  let α : ℝ → (lgManifold n).Form 1 := fun t =>
    (lgManifold n).rankTwoPrimitive (lambdaPotentialForm (ψ t)) (W (I.alongCoefficientPath t)) K
  have hα (t : Parameter) : (lgManifold n).IsSmoothForm
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm (ψ t.val))
        (W (I.alongCoefficientPath t.val)) K) :=
    (lgManifold n).isSmoothForm_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm (hψ t.val))
      (contMDiff_W_lgManifold _) _
  exact ⟨M.maslovAt (α := α) hα f parameterZero, M.maslovAt (α := α) hα f parameterOne,
    M.maslovAt_prescribed (α := α) hα f parameterZero rfl,
    M.maslovAt_prescribed (α := α) hα f parameterOne rfl,
    M.exists_grading (α := α) hα f⟩

/-- Specialize the constructed grading to the retained holomorphic arrow
of the toric comparison, with its actual inclusion markings at both ends. -/
theorem PotentialTailoringMarkedPrefix.exists_holomorphic_grading {n : ℕ}
    {I : ToricInput n} {φ : RealSpace n → ℝ} {β Cplus Aminus K : ℝ}
    {m : RoundingChoice} (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hK : 0 ≤ K) :
    ∃ s : P.holomorphic.deformation.source.Maslov,
    ∃ u : P.holomorphic.deformation.target.Maslov,
      IsLogarithmicGrading (P.holomorphic_ambient_marking.marking parameterZero).equiv s ∧
      IsLogarithmicGrading (P.holomorphic_ambient_marking.marking parameterOne).equiv u ∧
      Nonempty (GradedPairDeformation P.holomorphic.deformation s u) :=
  P.holomorphic_ambient_marking.exists_logarithmic_potential_grading
    hφ hc hlower (div_nonneg hK (sq_nonneg (Real.exp β)))

end FsFltz
