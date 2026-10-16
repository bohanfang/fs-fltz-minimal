import FsFltz.Geometry.IntrinsicBundleBoundaryDiffeomorph
import FsFltz.Geometry.IntrinsicBundlePrimitiveData

/-!
# Boundary form covariance of the transported primitive

Source: `geoemtric-part-fsf.tex`, `def:pair`, 132–146, `def:chain`,
163–169, and `sec:lean`, 788–814. The boundary primitive transports by
the actual boundary map induced by the ambient bundle transition. The
native inclusion square supplies the full tangent pullback equality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicBoundary

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Boundary restriction commutes with an actual native ambient pullback
whose boundary map has the literal inclusion square. -/
theorem restrictForm_nativePullback {q : ℕ}
    (α : IntrinsicLiouville.Form k M q) (f : M → M)
    (hf : ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ f)
    (h : Point k M → Point k M)
    (hh : ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ h)
    (hsquare : ∀ x, (h x).val = f x.val) :
    restrictForm (IntrinsicLiouville.nativePullbackForm f α) =
      (smoothManifold k M).pullback (smoothManifold k M) h (restrictForm α) := by
  let v := (Subtype.val : Point k M → M)
  have hmaps : f ∘ v = v ∘ h := funext (fun x => (hsquare x).symm)
  ext x vs
  have hd₁ := mfderiv_comp (I := 𝓘(ℝ, Model k)) (I' := 𝓡∂ (k + 1))
    (I'' := 𝓡∂ (k + 1)) x (hf.mdifferentiableAt (by simp))
      (contMDiff_val.mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, Model k))
    (I'' := 𝓡∂ (k + 1)) x (contMDiff_val.mdifferentiableAt (by simp))
      (hh.mdifferentiableAt (by simp))
  have hd : (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f x.val).comp
      (mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) v x) =
      (mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) v (h x)).comp
        (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) h x) := by
    rw [← hd₁, hmaps, hd₂]
  change α (f x.val) (fun i => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f x.val
      (mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) v x (vs i))) =
    α (h x).val (fun i => mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) v (h x)
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) h x (vs i)))
  rw [hsquare x]
  apply congrArg (α (f x.val))
  funext i
  exact congrArg (fun L => L (vs i)) hd

end FsFltz.Geometry.IntrinsicBoundary

namespace FsFltz.Geometry.IntrinsicSmoothBundle.BundlePrimitiveData

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace M E)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- The actual global primitive's boundary restriction is the pullback of
each original boundary form through that same ambient transition. -/
theorem boundary_formInTrivialization_eq_pullback (P : BundlePrimitiveData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (c : Trivialization M (π M E)) (hc : c ∈ trivializationAtlas M E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ c.baseSet) :
    IntrinsicBoundary.restrictForm (P.formInTrivialization e t) =
      (IntrinsicBoundary.smoothManifold k M).pullback (IntrinsicBoundary.smoothManifold k M)
        (compatibleBoundaryTransitionDiffeomorph e c he (compatibleTrivialization_of_mem hc) ht)
        (IntrinsicBoundary.restrictForm (P.form ⟨c, hc⟩ t)) := by
  rw [P.formInTrivialization_eq_pullback e he c hc ht]
  exact IntrinsicBoundary.restrictForm_nativePullback _ _ ((he c hc).1.contMDiff ht)
    _ (compatibleBoundaryTransitionDiffeomorph e c he (compatibleTrivialization_of_mem hc) ht).contMDiff
    (compatibleBoundaryTransitionDiffeomorph_val e c he (compatibleTrivialization_of_mem hc) ht)

end FsFltz.Geometry.IntrinsicSmoothBundle.BundlePrimitiveData
