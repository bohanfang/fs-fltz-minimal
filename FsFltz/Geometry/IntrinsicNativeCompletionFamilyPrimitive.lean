import FsFltz.Geometry.IntrinsicNativeCompletionFamilySmooth
import FsFltz.Geometry.IntrinsicCompletionFamilySlices

/-!
# Vertical primitive transport from the original completion family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–793 and 805–814.
The natural comparison preserves the native completed primitive on each
original slice. Its exact native and full-cylinder formulas, rather than a
primitive-preservation hypothesis, determine this equality. The primitive
on the fixed target presentation is the varying `completedPrimitive t`.
No one-form on the parameter direction is asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing
open SmoothManifold

variable {k d : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
  (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

local instance primitiveBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance primitiveBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

/-- A form on the original completion is determined by its native and
full-cylinder restrictions. The actual patch differentials are onto,
including at the original boundary. -/
theorem completionForm_eq_of_native_cylinder
    (α β : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      ∀ x, (α (original (fun p => C p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) x) =
      (β (original (fun p => C p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) x))
    (hcylinder : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold hδ C hemb hC hboundary hinv hzero) (cylinder (fun p => C p.val)) α =
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
        (completionManifold hδ C hemb hC hboundary hinv hzero) (cylinder (fun p => C p.val)) β) :
    α = β := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  funext x
  rcases jointly_surjective (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x with
    ⟨a, rfl⟩ | ⟨p, rfl⟩
  · exact SmoothManifold.form_eq_of_comp_eq (d := k + 1) (r := 1) (E := Model (k + 1)) _ _
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) a)
      (bijective_mfderiv_original hδ C hemb hC hboundary hinv hzero a).2 (hnative a)
  · exact SmoothManifold.form_eq_of_comp_eq (d := k + 1) (r := 1) (E := Model (k + 1)) _ _
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
        (cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) p)
      (bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero p).2 (congrFun hcylinder p)

/-- The exact native and cylindrical formulas of a smooth map into an
actual completion force its primitive pullback to be the original native
completed primitive. All radii of the constructed cylinder are used. -/
theorem pullback_completionPrimitive_of_native_cylinder
    (D : LiouvilleDomain d) (K : Completion D)
    (α : IntrinsicLiouville.Form k M 1)
    (i : M → D.domain.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) ∞ i)
    (hicarrier : ∀ x, i x ∈ D.domain.carrier)
    (hp : ∀ x, (D.liouville.primitive (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x) = α x)
    (b : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.domain.boundary)
    (hbp : (IntrinsicBoundary.smoothManifold k M).pullback D.domain.boundary b
      (D.domain.boundaryForm D.liouville.primitive) = IntrinsicBoundary.restrictForm α)
    (Λ : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hΛnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      ∀ x, (Λ (original (fun p => C p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) x) = α x)
    (hΛcylinder : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold hδ C hemb hC hboundary hinv hzero) (cylinder (fun p => C p.val)) Λ =
        cylinderPrimitive δ α)
    (f : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) → K.ambient.manifold.Point)
    (hf : letI := completionChartedSpace hδ C hemb hboundary hzero
      ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ f)
    (hfnative : ∀ x, f (original (fun p => C p.val) x) = K.inclusion.map (i x))
    (hfcylinder : ∀ p : Band δ (IntrinsicBoundary.Point k M),
      f (cylinder (fun p => C p.val) p) = K.endMap (b p.val.2, -p.val.1)) :
    (completionManifold hδ C hemb hC hboundary hinv hzero).pullback
      K.ambient.manifold f K.ambient.primitive = Λ := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
  apply completionForm_eq_of_native_cylinder hδ C hemb hC hboundary hinv hzero
  · intro x
    rw [hΛnative x]
    have he : f ∘ original c = K.inclusion.map ∘ i := funext hfnative
    have hd := mfderiv_comp x (hf.mdifferentiableAt (by simp))
      ((contMDiff_original hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    rw [he, mfderiv_comp x (K.inclusion.map.contMDiff.mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))] at hd
    have hk := K.primitive_on_domain (i x) (hicarrier x)
    ext vs
    let a : K.ambient.manifold.Point → Model d [⋀^Fin 1]→L[ℝ] ℝ := K.ambient.primitive
    change a (f (original c x)) (fun j =>
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) f (original c x)
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x (vs j))) = _
    have hdv (v : Model (k + 1)) :
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) K.inclusion.map (i x))
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x v) =
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) f (original c x))
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x v) :=
      congrArg (fun L : Model (k + 1) →L[ℝ] Model d => L v) hd
    calc
      _ = a (K.inclusion.map (i x)) (fun j =>
          mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) f (original c x)
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x (vs j))) :=
        congrArg (fun y => a y (fun j =>
          mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) f (original c x)
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x (vs j)))) (hfnative x)
      _ = a (K.inclusion.map (i x)) (fun j =>
          mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) K.inclusion.map (i x)
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x (vs j))) :=
        congrArg (a (K.inclusion.map (i x))) (funext (fun j => (hdv (vs j)).symm))
      _ = _ := (congrArg (fun A => A (fun j =>
          mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x (vs j))) hk).trans
        (congrArg (fun A => A vs) (hp x))
  · rw [hΛcylinder, ← P.pullback_comp X K.ambient.manifold
      (fun p => (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
      (fun x => hf.mdifferentiableAt (by simp))]
    let J : P.Point → D.domain.boundary.Point × ℝ := fun p => (b p.val.2, -p.val.1)
    have ht : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : P.Point => p.val.1) := contMDiff_fst.comp (contMDiff_band_val δ)
    have hJ : ContMDiff 𝓘(ℝ, Model (k + 1))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ J :=
      (b.contMDiff.comp (contMDiff_boundaryProjection δ)).prodMk
        ht.neg
    have he : f ∘ cylinder c = K.endMap ∘ J := funext hfcylinder
    rw [he]
    funext p
    ext vs
    have hvs : vs = fun _ : Fin 1 => vs 0 := by
      funext j
      rw [Fin.eq_zero j]
    rw [hvs]
    have hd := mfderiv_comp p (K.smooth_endMap.mdifferentiableAt (by simp))
      (hJ.mdifferentiableAt (by simp))
    change K.ambient.primitive (K.endMap (J p)) (fun _ =>
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) (K.endMap ∘ J) p (vs 0)) = _
    rw [hd]
    have hend := K.end_primitive (b p.val.2) (-p.val.1)
      (mfderiv 𝓘(ℝ, Model (k + 1))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) J p (vs 0)).1
      (mfderiv 𝓘(ℝ, Model (k + 1))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) J p (vs 0)).2
    change K.ambient.primitive (K.endMap (J p)) (fun _ =>
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) K.endMap (J p)
        (mfderiv 𝓘(ℝ, Model (k + 1))
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) J p (vs 0))) = _
    have hend' : K.ambient.primitive (K.endMap (J p)) (fun _ =>
        mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) K.endMap (J p)
          (mfderiv 𝓘(ℝ, Model (k + 1))
            ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) J p (vs 0))) =
      Real.exp (-p.val.1) * evalOne (D.domain.boundaryForm D.liouville.primitive)
        (b p.val.2) (mfderiv 𝓘(ℝ, Model (k + 1))
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) J p (vs 0)).1 := by
      simpa only [Prod.eta, evalOne, J] using hend
    rw [hend']
    have hfirst : (mfderiv 𝓘(ℝ, Model (k + 1))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) J p (vs 0)).1 =
      mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (d - 1)) b p.val.2
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection p (vs 0)) := by
      change (mfderiv 𝓘(ℝ, Model (k + 1))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        (fun q => ((b ∘ boundaryProjection) q, -q.val.1)) p (vs 0)).1 = _
      rw [mfderiv_prodMk
        ((b.contMDiff.comp (contMDiff_boundaryProjection δ)).mdifferentiableAt (by simp))
        (ht.neg.mdifferentiableAt (by simp)),
        mfderiv_comp p (b.contMDiff.mdifferentiableAt (by simp))
          ((contMDiff_boundaryProjection δ).mdifferentiableAt (by simp))]
      rfl
    rw [hfirst]
    have hbval := congrArg (fun A => A (fun _ =>
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection p (vs 0)))
      (congrFun hbp p.val.2)
    exact congrArg (fun s : ℝ => Real.exp (-p.val.1) * s) hbval

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing SmoothManifold

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The jointly smooth original quotient comparison transports exactly the
vertical completed primitive of this same pair deformation. The target
primitive varies with the parameter in the fixed source presentation. -/
theorem pullback_completedPrimitive_ambientNativeTotalMap
    (Q : PairDeformation n)
    (α : Parameter → IntrinsicLiouville.Form k M 1)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (hbp : ∀ t, (IntrinsicBoundary.smoothManifold k M).pullback
      (Q.pair t).ambientDomain.domain.boundary (b t)
      ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
        IntrinsicBoundary.restrictForm (α t))
    (hsquareB : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
    {δ : ℝ} (hδ : 0 < δ)
    (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
    (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞
      (C t) (Half δ (IntrinsicBoundary.Point k M)))
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
      ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
          ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
    (hzero : ∀ t (b : IntrinsicBoundary.Point k M), C t (0, b) = b.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (Λ : ∀ t, (completionManifold hδ (C t) (hemb t) (hC t)
      (hboundary t) (hinv t) (hzero t)).Form 1)
    (hΛnative : ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
      ∀ x, (Λ t (original (fun p => C t p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) x) = α t x)
    (hΛcylinder : ∀ t, (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t))
      (cylinder (fun p => C t p.val)) (Λ t) = cylinderPrimitive δ (α t))
    (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Q.source.ambientCompletion.ambient.manifold.Point)
    (hq : letI := totalFamilyChartedSpace hδ C hzero hjoint
      ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ q)
    (hqnative : ∀ t x, q (original (totalCollar (fun t p => C t p.val)) (t, x)) =
      Q.ambientNativeReferenceMap e t x)
    (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      q (totalCylinder (fun t p => C t p.val) (t, p)) =
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))
    (t : Parameter) :
    (completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t)).pullback
      Q.source.ambientCompletion.ambient.manifold
      (q ∘ sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t)
      (Q.completedPrimitive t) = Λ t := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let X := completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t)
  let p := Q.ambientCompletionPresentation t
  let qs := q ∘ sliceIn c t
  have hqs : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ qs :=
    hq.comp (contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t)
  change X.pullback Q.source.ambientCompletion.ambient.manifold qs
    (Q.source.ambientCompletion.ambient.manifold.pullback
      (Q.pair t).ambientCompletion.ambient.manifold p.equiv
      (Q.pair t).ambientCompletion.ambient.primitive) = Λ t
  rw [← X.pullback_comp Q.source.ambientCompletion.ambient.manifold
    (Q.pair t).ambientCompletion.ambient.manifold
    (fun x => hqs.mdifferentiableAt (by simp))
    (fun x => p.equiv.contMDiff.mdifferentiableAt (by simp))]
  apply pullback_completionPrimitive_of_native_cylinder hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t) (Q.pair t).ambientDomain
    (Q.pair t).ambientCompletion (α t) (fun x => (e t x).val)
    ((Q.pair t).ambientDomain.domain.contMDiff_subtype_val.comp (e t).contMDiff)
    (fun x => (e t x).property) (hp t) (b t) (hbp t) (Λ t) (hΛnative t) (hΛcylinder t)
    (p.equiv ∘ qs) (p.equiv.contMDiff.comp hqs)
  · intro x
    change p.equiv (q (sliceIn c t (original (c t) x))) = _
    rw [sliceIn_original, hqnative]
    exact p.equiv.apply_symm_apply _
  · intro z
    change p.equiv (q (sliceIn c t (cylinder (c t) z))) = _
    rw [sliceIn_cylinder, hqend]
    change p.equiv (p.equiv.symm ((Q.pair t).ambientCompletion.endMap
      ((Q.ambientPresentation t).boundaryEquiv (b parameterZero z.val.2), -z.val.1))) = _
    rw [p.equiv.apply_symm_apply, hsquareB]

end FsFltz.Geometry.PairDeformation
