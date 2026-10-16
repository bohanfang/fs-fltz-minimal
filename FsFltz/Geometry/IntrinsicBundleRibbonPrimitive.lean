import FsFltz.Geometry.IntrinsicBundleBoundaryForm
import FsFltz.Geometry.IntrinsicBundleRibbonData
import FsFltz.Geometry.IntrinsicBundleWitnessData

/-!
# The original ribbon primitive equation in the same global charts

Source: `geoemtric-part-fsf.tex`, `def:pair`, 132–146, `def:chain`,
163–169, and `sec:lean`, 788–814. Actual ambient boundary and ribbon
coordinate squares transport the witnessed primitive equation on full
native tangent spaces. The equation is required only on original local
charts; it is proved for the constructed compatible presentation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {a k : ℕ} {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Witnessed primitive matching transports through actual native source
and boundary maps with their full tangent pullback and point squares. -/
theorem ribbon_primitive_eq_of_pullback
    (lamG lamL : Form a A 1) (μG μL : Form k M 1)
    (R : M → M) (hR : ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ R)
    (h : IntrinsicBoundary.Point a A → IntrinsicBoundary.Point a A)
    (hh : ContMDiff 𝓘(ℝ, Model a) 𝓘(ℝ, Model a) ∞ h)
    (jG jL : M → IntrinsicBoundary.Point a A)
    (hjG : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) ∞ jG)
    (hjL : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) ∞ jL)
    (bG bL : IntrinsicBoundary.Point a A → ℝ)
    (hlam : IntrinsicBoundary.restrictForm lamG =
      (IntrinsicBoundary.smoothManifold a A).pullback (IntrinsicBoundary.smoothManifold a A)
        h (IntrinsicBoundary.restrictForm lamL))
    (hμ : μG = nativePullbackForm R μL)
    (hsquare : ∀ x, h (jG x) = jL (R x))
    (hb : ∀ x, bG x = bL (h x))
    (hribbon : ∀ x,
      ((bL (jL x) • IntrinsicBoundary.restrictForm lamL (jL x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) jL x) = μL x) :
    ∀ x, ((bG (jG x) • IntrinsicBoundary.restrictForm lamG (jG x))).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) jG x) = μG x := by
  intro x
  have hmaps : h ∘ jG = jL ∘ R := funext hsquare
  have hd₁ := mfderiv_comp x (hh.mdifferentiableAt (by simp)) (hjG.mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp x (hjL.mdifferentiableAt (by simp)) (hR.mdifferentiableAt (by simp))
  have hd : (mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model a) h (jG x)).comp
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) jG x) =
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) jL (R x)).comp
        (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) R x) := by
    rw [← hd₁, hmaps, hd₂]
  rw [hμ]
  ext vs
  have hα := congrFun hlam (jG x)
  change bG (jG x) * IntrinsicBoundary.restrictForm lamG (jG x)
      (fun i => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) jG x (vs i)) =
    μL (R x) (fun i => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) R x (vs i))
  rw [hb (jG x), hα]
  change bL (h (jG x)) * IntrinsicBoundary.restrictForm lamL (h (jG x))
      (fun i => mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model a) h (jG x)
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) jG x (vs i))) = _
  have hvec (v : TangentSpace (𝓡∂ (k + 1)) x) :
      mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model a) h (jG x)
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) jG x v) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) jL (R x)
        (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) R x v) :=
    congrArg (fun L => L v) hd
  simp_rw [hvec]
  rw [hsquare x]
  exact congrArg (fun L => L (fun i => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) R x (vs i)))
    (hribbon (R x))

variable {ER : Parameter → Type*} [∀ t, TopologicalSpace (ER t)]
  [TopologicalSpace (TotalSpace M ER)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) ER]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]

/-- The original local witnessed primitive equation holds in the same
two constructed charts as the primitive, ribbon map and positive witness.
No transported primitive-matching hypothesis is supplied. -/
theorem BundleRibbonData.primitive_eq_in_compatible_charts
    (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) ER EA)
    (PA : BundlePrimitiveData (k := a) (M := A) EA)
    (PM : BundlePrimitiveData (k := k) (M := M) ER)
    (PW : BundleWitnessData (k := a) (M := A) EA)
    (eR : Trivialization M (π M ER)) (heR : CompatibleTrivialization (𝓡∂ (k + 1)) ER eR)
    (eA : Trivialization A (π A EA)) (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet))
    (hribbon : ∀ x,
      ((PW.witness ⟨cA, hcA⟩ t (PJ.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t x) •
        IntrinsicBoundary.restrictForm (PA.form ⟨cA, hcA⟩ t)
          (PJ.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (PJ.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t) x) =
          PM.form ⟨cR, hcR⟩ t x) :
    ∀ x, ((PW.witnessInTrivialization eA heA t (PJ.mapInTrivializations eR eA heA t x) •
      IntrinsicBoundary.restrictForm (PA.formInTrivialization eA t)
        (PJ.mapInTrivializations eR eA heA t x))).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (PJ.mapInTrivializations eR eA heA t) x) =
        PM.formInTrivialization eR t x := by
  let h := compatibleBoundaryTransitionDiffeomorph eA cA heA (compatibleTrivialization_of_mem hcA) ht.2
  have hjG := (PJ.smooth_in_compatible_charts eR heR eA heA).contMDiff_slice
    (IntrinsicBoundary.smoothManifold a A) t ⟨ht.1.1, ht.2.1⟩
  have hjL := (PJ.smooth ⟨cR, hcR⟩ ⟨cA, hcA⟩).contMDiff_slice
    (IntrinsicBoundary.smoothManifold a A) t ⟨ht.1.2, ht.2.2⟩
  have hsquare (x : M) : h (PJ.mapInTrivializations eR eA heA t x) =
      PJ.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t (eR.coordChange cR t x) := by
    apply Subtype.ext
    rw [compatibleBoundaryTransitionDiffeomorph_val,
      PJ.mapInTrivializations_eq_local_val eR eA heA cR hcR cA hcA ht x,
      cA.coordChange_coordChange eA cA ht.2.2 ht.2.1, cA.coordChange_same ht.2.2]
    rfl
  exact ribbon_primitive_eq_of_pullback
    (PA.formInTrivialization eA t) (PA.form ⟨cA, hcA⟩ t)
    (PM.formInTrivialization eR t) (PM.form ⟨cR, hcR⟩ t)
    (eR.coordChange cR t) ((heR cR hcR).1.contMDiff ht.1)
    h h.contMDiff (PJ.mapInTrivializations eR eA heA t) (PJ.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t)
    hjG hjL (PW.witnessInTrivialization eA heA t) (PW.witness ⟨cA, hcA⟩ t)
    (PA.boundary_formInTrivialization_eq_pullback eA heA cA hcA ht.2)
    (PM.formInTrivialization_eq_pullback eR heR cR hcR ht.1)
    hsquare (PW.witnessInTrivialization_eq eA heA cA hcA ht.2) hribbon

end FsFltz.Geometry.IntrinsicSmoothBundle
