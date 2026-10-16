import FsFltz.Geometry.TailoringCompletedGradingTransport
import FsFltz.Geometry.TailoringCompletedGradingWeight

/-!
# Native grading extends through the retained cylindrical family

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030.
The actual native family is pulled through the retained original
presentations, restricted to the fixed localized zero slice, then stretched
by its fixed radial weight. This constructs a Maslov family for the actual
completed primitives, with joint regularity across the compact/end seam.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
namespace LocalizedCompletionFamily
variable {n : ℕ} {D : CompactDomain (2 * n)} {L : Parameter → LiouvilleStructure D}

/-- The literal original primitive in the retained zero-slice presentation. -/
def nativePresentedPrimitive (F : LocalizedCompletionFamily D L)
    (α : ℝ → D.extension.Form 1) (t : ℝ) :
    (F.collars parameterZero).localizedDomain.domain.extension.Form 1 :=
  (F.collars parameterZero).localizedDomain.domain.extension.pullback D.extension
    (F.collars parameterZero).originalInclusion.map
      (D.extension.pullback D.extension (F.originalPresentation t).extensionEquiv (α t))

/-- The explicit complex field on the retained zero-slice completion. -/
def completedNativeComplex (F : LocalizedCompletionFamily D L)
    (α : ℝ → D.extension.Form 1) (J : ℝ → AlmostComplexField D.extension) (t : ℝ) :
    AlmostComplexField (F.collars parameterZero).localizedDomain.domain.extension := fun x =>
  rankTwoShearComplex (normalizedWeightDifferential
    (M := (F.collars parameterZero).localizedDomain.domain.extension)
    (fun z => (F.collars parameterZero).radialWeight z.val) x)
    ((F.collars parameterZero).localizedDomain.domain.extension.liouvilleVector
      (F.nativePresentedPrimitive α t) x) 1
    (pullbackAlmostComplex D.extension D.extension (F.originalPresentation t).extensionEquiv
      (J t) x.val.val)

/-- The explicit squared tensor uses the same shear and the same presentation. -/
def completedNativeTensor (F : LocalizedCompletionFamily D L)
    (α : ℝ → D.extension.Form 1) (τ : ℝ → D.extension.Point → SquaredCanonicalTensor n) (t : ℝ) :
    (F.collars parameterZero).localizedDomain.domain.extension.Point → SquaredCanonicalTensor n := fun x =>
  rankTwoShearTensor (normalizedWeightDifferential
    (M := (F.collars parameterZero).localizedDomain.domain.extension)
    (fun z => (F.collars parameterZero).radialWeight z.val) x)
    ((F.collars parameterZero).localizedDomain.domain.extension.liouvilleVector
      (F.nativePresentedPrimitive α t) x) 1
    (pullbackSquaredTensor D.extension D.extension (F.originalPresentation t).extensionEquiv
      (τ t) x.val.val)

/-- The full completed formulas recover the exact native pulled fields
on every compact point, including the boundary seam. -/
theorem completedNative_eq_on_carrier (F : LocalizedCompletionFamily D L)
    (α : ℝ → D.extension.Form 1) (J : ℝ → AlmostComplexField D.extension)
    (τ : ℝ → D.extension.Point → SquaredCanonicalTensor n) (t : ℝ)
    (x : (F.collars parameterZero).localizedDomain.domain.extension.Point)
    (hx : x ∈ (F.collars parameterZero).localizedDomain.domain.carrier) :
    F.completedNativeComplex α J t x =
      pullbackAlmostComplex D.extension D.extension (F.originalPresentation t).extensionEquiv
        (J t) x.val.val ∧
    F.completedNativeTensor α τ t x =
      pullbackSquaredTensor D.extension D.extension (F.originalPresentation t).extensionEquiv
        (τ t) x.val.val := by
  unfold completedNativeComplex completedNativeTensor
  rw [(F.collars parameterZero).normalizedRadialWeightDifferential_eq_zero_of_mem_carrier x hx]
  constructor
  · simp [rankTwoShearComplex, rankTwoShear]
  · ext v
    simp [rankTwoShearTensor, rankTwoShear]

/-- At the source, the completed family's explicit fields agree on the
entire compact carrier with the cylindrical extension of the chosen native
source representative. This includes boundary points. -/
theorem completedNative_zero_eq_on_carrier (F : LocalizedCompletionFamily D L)
    (α : ℝ → D.extension.Form 1) (J : ℝ → AlmostComplexField D.extension)
    (τ : ℝ → D.extension.Point → SquaredCanonicalTensor n)
    (s : MaslovRepresentative D.extension
      (D.extension.exteriorDerivative (L parameterZero).primitive))
    (hJ : J 0 = s.J) (hτ : τ 0 = s.tensor)
    (x : (F.collars parameterZero).localizedDomain.domain.extension.Point)
    (hx : x ∈ (F.collars parameterZero).localizedDomain.domain.carrier) :
    F.completedNativeComplex α J 0 x =
      ((F.collars parameterZero).cylindricalMaslovOfNative s).J x ∧
    F.completedNativeTensor α τ 0 x =
      ((F.collars parameterZero).cylindricalMaslovOfNative s).tensor x := by
  have he : (F.originalPresentation 0).extensionEquiv =
      Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) D.extension.Point ∞ := by
    ext y
    exact F.originalPresentation_zero y
  obtain ⟨hsourceJ, hsourceT⟩ := F.completedNative_eq_on_carrier α J τ 0 x hx
  rw [he, pullbackAlmostComplex_refl, hJ] at hsourceJ
  rw [he, pullbackSquaredTensor_refl, hτ] at hsourceT
  obtain ⟨hcompletedJ, hcompletedT⟩ :=
    (F.collars parameterZero).cylindricalMaslovOfNative_eq_on_carrier s x hx
  exact ⟨hsourceJ.trans hcompletedJ.symm, hsourceT.trans hcompletedT.symm⟩

/-- The derivative of the actual localized presentation is the original
presentation's derivative, because both native projections have identity
derivative. -/
theorem mfderiv_compactPresentation_eq_original (F : LocalizedCompletionFamily D L)
    (t : Parameter) (x : (F.collars parameterZero).localizedDomain.domain.extension.Point) :
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      (F.compactPresentation t).extensionEquiv x =
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      (F.originalPresentation t.val).extensionEquiv x.val.val := by
  have he : (F.collars t).originalInclusion.map ∘ (F.compactPresentation t).extensionEquiv =
      (F.originalPresentation t.val).extensionEquiv ∘
        (F.collars parameterZero).originalInclusion.map := funext (F.original_projection t)
  have hd : mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      ((F.collars t).originalInclusion.map ∘ (F.compactPresentation t).extensionEquiv) x =
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      ((F.originalPresentation t.val).extensionEquiv ∘
        (F.collars parameterZero).originalInclusion.map) x := by rw [he]
  rw [mfderiv_comp x ((F.collars t).originalInclusion.map.contMDiff.mdifferentiableAt (by simp))
      ((F.compactPresentation t).extensionEquiv.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp x ((F.originalPresentation t.val).extensionEquiv.contMDiff.mdifferentiableAt (by simp))
      ((F.collars parameterZero).originalInclusion.map.contMDiff.mdifferentiableAt (by simp)),
    (F.collars t).mfderiv_originalInclusion, (F.collars parameterZero).mfderiv_originalInclusion] at hd
  ext v
  exact congrArg (fun A => A v) hd

/-- At any parameter, the explicit completed family tensor agrees on the
compact carrier with the actual presentation pullback of that slice's
cylindrical native tensor. -/
theorem completedNativeTensor_eq_pullback_cylindrical_on_carrier
    (F : LocalizedCompletionFamily D L) (α : ℝ → D.extension.Form 1)
    (τ : ℝ → D.extension.Point → SquaredCanonicalTensor n) (t : Parameter)
    (s : MaslovRepresentative D.extension
      (D.extension.exteriorDerivative (L t).primitive)) (hτ : τ t.val = s.tensor)
    (x : (F.collars parameterZero).localizedDomain.domain.extension.Point)
    (hx : x ∈ (F.collars parameterZero).localizedDomain.domain.carrier) :
    F.completedNativeTensor α τ t.val x =
      pullbackSquaredTensor (F.collars parameterZero).localizedDomain.domain.extension
        (F.collars t).localizedDomain.domain.extension (F.completionPresentation t).equiv
        ((F.collars t).cylindricalMaslovOfNative s).tensor x := by
  rw [(F.completedNative_eq_on_carrier α (fun _ => s.J) τ t.val x hx).2,
    F.completionPresentation_eq t]
  have hy : (F.compactPresentation t).extensionEquiv x ∈
      (F.collars t).localizedDomain.domain.carrier := by
    rw [← (F.compactPresentation t).carrier]
    exact mem_image_of_mem _ hx
  unfold pullbackSquaredTensor
  rw [((F.collars t).cylindricalMaslovOfNative_eq_on_carrier s _ hy).2,
    F.original_projection t, F.mfderiv_compactPresentation_eq_original t x, hτ]

/-- Undoing the actual completion presentation recovers the slice's native
cylindrical tensor on its full compact carrier. -/
theorem pullback_completedNativeTensor_eq_cylindrical_on_carrier
    (F : LocalizedCompletionFamily D L) (α : ℝ → D.extension.Form 1)
    (τ : ℝ → D.extension.Point → SquaredCanonicalTensor n) (t : Parameter)
    (s : MaslovRepresentative D.extension
      (D.extension.exteriorDerivative (L t).primitive)) (hτ : τ t.val = s.tensor)
    (x : (F.collars t).localizedDomain.domain.extension.Point)
    (hx : x ∈ (F.collars t).localizedDomain.domain.carrier) :
    pullbackSquaredTensor (F.collars t).localizedDomain.domain.extension
      (F.collars parameterZero).localizedDomain.domain.extension (F.completionPresentation t).equiv.symm
      (F.completedNativeTensor α τ t.val) x =
        ((F.collars t).cylindricalMaslovOfNative s).tensor x := by
  let e : (F.collars parameterZero).localizedDomain.domain.extension.SmoothEquiv
      (F.collars t).localizedDomain.domain.extension := (F.completionPresentation t).equiv
  have hy : e.symm x ∈ (F.collars parameterZero).localizedDomain.domain.carrier := by
    obtain ⟨y, hy, he⟩ : x ∈ (F.compactPresentation t).extensionEquiv ''
        (F.collars parameterZero).localizedDomain.domain.carrier := by
      rw [(F.compactPresentation t).carrier]
      exact hx
    change (F.completionPresentation t).equiv.symm x ∈ _
    rw [F.completionPresentation_eq t, ← he]
    change (F.compactPresentation t).extensionEquiv.symm
      ((F.compactPresentation t).extensionEquiv y) ∈ _
    simpa only [Diffeomorph.symm_apply_apply] using hy
  have hslice := F.completedNativeTensor_eq_pullback_cylindrical_on_carrier α τ t s hτ (e.symm x) hy
  have hcancel := congrFun (pullbackSquaredTensor_trans
    (F.collars t).localizedDomain.domain.extension
    (F.collars parameterZero).localizedDomain.domain.extension
    (F.collars t).localizedDomain.domain.extension e.symm e
    ((F.collars t).cylindricalMaslovOfNative s).tensor) x
  rw [Diffeomorph.symm_trans_self, pullbackSquaredTensor_refl] at hcancel
  calc
    _ = pullbackSquaredTensor (F.collars t).localizedDomain.domain.extension
      (F.collars parameterZero).localizedDomain.domain.extension e.symm
      (pullbackSquaredTensor (F.collars parameterZero).localizedDomain.domain.extension
        (F.collars t).localizedDomain.domain.extension e
        ((F.collars t).cylindricalMaslovOfNative s).tensor) x := by
      exact congrArg (fun T : SquaredCanonicalTensor n => T.compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e.symm x)) hslice
    _ = _ := hcancel.symm

/-- A native Maslov family extends over the same retained cylindrical
completion family. The completed grading and all its regularity are
constructed from the native family and the already retained geometry. -/
theorem exists_completedMaslovFamily_with_native_formula (F : LocalizedCompletionFamily D L)
    (α : ℝ → D.extension.Form 1) (hα : D.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val = (L t).primitive)
    (s : MaslovFamily D.extension (fun t => D.extension.exteriorDerivative (α t)))
    (η : ℝ → (F.collars parameterZero).localizedDomain.domain.extension.Form 2)
    (hη : ∀ t : Parameter, η t.val =
      (F.collars parameterZero).localizedDomain.domain.extension.exteriorDerivative
        ((F.collars parameterZero).localizedDomain.domain.extension.pullback
          (F.collars t).localizedDomain.domain.extension (F.completionPresentation t).equiv
            (F.collars t).cylindricalCompletion.ambient.primitive)) :
    ∃ g : MaslovFamily (F.collars parameterZero).localizedDomain.domain.extension η,
      (∀ t : Parameter, g.J t.val = F.completedNativeComplex α s.J t.val) ∧
      ∀ t : Parameter, g.tensor t.val = F.completedNativeTensor α s.tensor t.val := by
  let C := F.collars parameterZero
  let E : LiouvilleDomain (2 * n) := ⟨D, L parameterZero⟩
  let N := E.neighborhoodDomain.extension
  let M := C.localizedDomain.domain.extension
  let e := fun t : ℝ => (F.originalPresentation t).extensionEquiv
  let αp := fun t => D.extension.pullback D.extension (e t) (α t)
  have hαp : D.extension.IsSmoothFormFamily αp :=
    D.extension.isSmoothFormFamily_pullback_one_of_contMDiff_family D.extension
      (fun t x => e t x) F.smooth_originalPresentation α hα
  have he : D.extension.IsSmoothIntervalMapFamily D.extension
      (fun t : Parameter => e t.val) :=
    ⟨(fun t x => e t x), ⟨univ, isOpen_univ, subset_univ _, F.smooth_originalPresentation.contMDiffOn⟩,
      fun _ => rfl⟩
  obtain ⟨sp, hspJ, hspT⟩ := s.exists_intervalPullback (fun t => e t.val) he
    (fun t => D.extension.exteriorDerivative (αp t)) (fun t =>
      (D.extension.exteriorDerivative_pullback D.extension (e t.val).toContMDiffMap
        (α t.val) (hα.slice t.property)).symm)
  let αr := fun t => N.pullback D.extension Subtype.val (αp t)
  have hαr (t : ℝ) (ht : t ∈ parameterInterval) : N.IsSmoothForm (αr t) :=
    N.isSmoothForm_pullback_one D.extension
      ⟨Subtype.val, contMDiff_subtype_val⟩ (αp t) (hαp.slice ht)
  let sr := (sp.restrictPrimitive (fun _ ht => hαp.slice ht) E.symplecticNeighborhood).restrictPrimitive
    hαr C.neighborhood
  let χ := fun t => M.pullback D.extension C.originalInclusion.map (αp t)
  have hχ : M.IsSmoothFormFamily χ :=
    M.isSmoothFormFamily_pullback_one D.extension C.originalInclusion.map αp hαp
  have hχr (t : ℝ) : χ t = M.pullback N Subtype.val (αr t) :=
    M.pullback_comp N D.extension
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n))) (n := ∞)).mdifferentiable (by simp))
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n))) (n := ∞)).mdifferentiable (by simp))
      (αp t)
  let sc : MaslovFamily M (fun t => M.exteriorDerivative (χ t)) :=
    { sr with compatible := fun t ht => by rw [hχr t]; exact sr.compatible t ht }
  have hχeq (t : Parameter) : χ t.val = M.pullback
      (F.collars t).localizedDomain.domain.extension (F.compactPresentation t).extensionEquiv
        (F.collars t).localizedDomain.liouville.primitive := by
    rw [F.compactPrimitive_eq_originalPullback t]
    dsimp only [χ, αp, e]
    rw [hαeq t]
  have hnd : ∀ t ∈ parameterInterval, ∀ x, M.Nondegenerate (M.exteriorDerivative (χ t)) x := by
    intro t ht x v hv
    by_contra h
    have hp := (sc.compatible t ht).2.2.2 x v h
    rw [hv (sc.J t x v)] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  let Z := fun t => M.liouvilleVector (χ t)
  have hZ : M.IsSmoothVectorFieldFamily Z := M.isSmoothVectorFieldFamily_liouvilleVector χ hχ hnd
  have hcon : ∀ t ∈ parameterInterval, ∀ x v,
      evalTwo (M.exteriorDerivative (χ t)) x (Z t x) v = evalOne (χ t) x v := by
    intro t ht x
    exact M.liouvilleVector_contraction (χ t) x
      (M.liouvilleEquation_exists (χ t) x (hnd t ht x))
  let w := fun z : M.Point => C.radialWeight z.val
  have hweight (t : Parameter) :
      (fun x => w x • χ t.val x) = M.pullback
        (F.collars t).localizedDomain.domain.extension (F.completionPresentation t).equiv
          (F.collars t).cylindricalCompletion.ambient.primitive := by
    rw [F.completedPrimitive_eq_radialWeight_smul t, hχeq t]
  have hden : ∀ t ∈ parameterInterval, ∀ x,
      1 + normalizedWeightDifferential (M := M) w x (Z t x) ≠ 0 := by
    intro t ht x
    apply normalizedWeightDifferential_denominator_ne_zero (hχ.slice ht) w C.smooth_radialWeight
      x (C.radialWeight_positive x.val).ne' (hnd t ht x) _ (Z t x) (hcon t ht x)
    rw [hweight ⟨t, ht⟩]
    exact (F.collars ⟨t, ht⟩).cylindricalCompletion.ambient.nondegenerate_pullback_primitive
      M (F.completionPresentation ⟨t, ht⟩).equiv x
  let sw := sc.rescalePrimitive (fun _ ht => hχ.slice ht) Z hZ hcon w C.smooth_radialWeight
    (fun x => C.radialWeight_positive x.val) hden
  have hcompatible : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M (η t) (sw.J t) := by
    intro t ht
    rw [hη ⟨t, ht⟩, ← hweight ⟨t, ht⟩]
    exact sw.compatible t ht
  let g : MaslovFamily M η := { sw with compatible := hcompatible }
  refine ⟨g, ?_, ?_⟩
  · intro t
    funext x
    change rankTwoShearComplex _ _ 1 (sp.J t.val x.val.val) = _
    rw [hspJ t]
    rfl
  · intro t
    funext x
    change rankTwoShearTensor _ _ 1 (sp.tensor t.val x.val.val) = _
    rw [hspT t]
    rfl

end LocalizedCompletionFamily
end FsFltz.Geometry
