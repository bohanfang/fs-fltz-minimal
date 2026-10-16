import FsFltz.Geometry.IntrinsicLiouvilleMapExtension

/-!
# Tangent and primitive transport for a prescribed native compact map

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189, and
`sec:lean`, lines 805–814. A commuting square for the prescribed native
diffeomorphism determines the full differential of any actual smooth
ambient extension along its carrier. Bijective inclusion tangents therefore
give immersion of that same extension and allow the native primitive
identity to descend to its ambient carrier identity.

These diagram lemmas do not supply the inclusions or map extension. They
serve the separate construction of independently presented native maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry.NativeCompactMap

variable {k : ℕ} {M N : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (k + 1)) N]

/-- Differentiate the prescribed native map square in all native tangent
directions, including at boundary points. -/
theorem differential_square (A B : SmoothManifold (k + 1))
    (i : M → A.Point) (j : N → B.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hj : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j)
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (f : A.Point → B.Point)
    (hf : ∀ x, MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f (i x))
    (hsquare : ∀ x, f (i x) = j (h x)) (x : M) :
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f (i x)).comp
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) =
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j (h x)).comp
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) := by
  have hfi := mfderiv_comp (f := i) (g := f) x (hf x) (hi.mdifferentiableAt (by simp))
  have hjh := mfderiv_comp (f := h) (g := j) x
    (hj.mdifferentiableAt (by simp)) (h.mdifferentiable (by simp) x)
  have he : f ∘ i = j ∘ h := funext hsquare
  rw [he] at hfi
  exact hfi.symm.trans hjh

/-- Native tangent bijections and the differentiated native map square
prove immersion of the actual ambient extension on the native carrier. -/
theorem injective_mfderiv_of_native_square (A B : SmoothManifold (k + 1))
    (i : M → A.Point) (j : N → B.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hj : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j)
    (hibij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hjbij : ∀ y, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j y))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (f : A.Point → B.Point)
    (hf : ∀ x, MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f (i x))
    (hsquare : ∀ x, f (i x) = j (h x)) (x : M) :
    Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f (i x)) := by
  intro v w hvw
  obtain ⟨v', rfl⟩ := (hibij x).2 v
  obtain ⟨w', rfl⟩ := (hibij x).2 w
  apply congrArg (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)
  apply (h.isInvertible_mfderiv (by simp)).injective
  apply (hjbij (h x)).1
  change ((mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j (h x)).comp
    (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x)) v' =
      ((mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j (h x)).comp
        (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x)) w'
  rw [← differential_square A B i j hi hj h f hf hsquare x]
  exact hvw

/-- Native primitive scaling descends to the original ambient extension
along the carrier. Surjectivity of the source inclusion's full tangent map
detects equality of the actual ambient covectors. -/
theorem primitive_scaled_of_native_square (A B : SmoothManifold (k + 1))
    (i : M → A.Point) (j : N → B.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hj : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j)
    (hibij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (f : A.Point → B.Point)
    (hf : ∀ x, MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f (i x))
    (hsquare : ∀ x, f (i x) = j (h x))
    (lam : A.Form 1) (mu : B.Form 1)
    (α : IntrinsicLiouville.Form k M 1) (β : IntrinsicLiouville.Form k N 1)
    (hiα : ∀ x, (lam (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α x)
    (hjβ : ∀ y, (mu (j y)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j y) = β y)
    (c : ℝ)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) (x : M) :
    A.pullback B f mu (i x) = c • lam (i x) := by
  ext vs
  let ws : Fin 1 → TangentSpace (𝓡∂ (k + 1)) x :=
    fun a => ((hibij x).2 (vs a)).choose
  have hws (a : Fin 1) :
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x (ws a) = vs a :=
    ((hibij x).2 (vs a)).choose_spec
  have hd (a : Fin 1) :
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f (i x) (vs a) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j (h x)
        (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x (ws a)) := by
    rw [← hws a]
    exact congrArg (fun L => L (ws a)) (differential_square A B i j hi hj h f hf hsquare x)
  have hs := congrArg (fun L => L ws) (hscale x)
  have hsα := congrArg (fun L => L ws) (hiα x)
  have hsβ := congrArg (fun L => L
    (fun a => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x (ws a))) (hjβ (h x))
  change β (h x) (fun a => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x (ws a)) =
    c * α x ws at hs
  change lam (i x) (fun a => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x (ws a)) =
    α x ws at hsα
  change mu (j (h x)) (fun a =>
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j (h x)
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x (ws a))) =
    β (h x) (fun a => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x (ws a)) at hsβ
  change mu (f (i x))
    (fun a => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f (i x) (vs a)) =
      c * lam (i x) vs
  erw [hsquare x, show (fun a => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    f (i x) (vs a)) = _ from funext hd]
  exact hsβ.trans (hs.trans (by simpa only [hws] using congrArg (fun r : ℝ => c * r) hsα.symm))

end FsFltz.Geometry.NativeCompactMap
