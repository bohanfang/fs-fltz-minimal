import FsFltz.Geometry.IntrinsicNativeCompletionFamilyPrimitive

/-!
# Spatial differentials and fields from native primitive transport

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 175–189; and `sec:lean`, lines 788–793 and 805–812.
The established vertical primitive equation implies an invertible spatial
differential in equal dimension. It also transports the actual Liouville
field. These consequences require neither a supplied completed inverse nor
an extra field-transport hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.SmoothManifold

/-- A nondegenerate actual pullback two-form forces the spatial
differential to be injective. This statement requires no inverse map. -/
theorem injective_mfderiv_of_nondegenerate_pullback {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : M.Point → N.Point) (η : N.Form 2) (x : M.Point)
    (hnd : M.Nondegenerate (M.pullback N f η) x) :
    Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply hnd v
  intro w
  change η (f x) (fun j =>
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x (![v, w] j)) = 0
  exact (η (f x)).map_coord_zero (i := 0) hv

/-- Equal-dimensional primitive transport and source symplecticity give
a bijective actual differential at every spatial point. -/
theorem bijective_mfderiv_of_nondegenerate_primitive_pullback {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (hdim : d = e)
    (f : M.Point → N.Point)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f)
    (α : M.Form 1) (β : N.Form 1) (hβ : N.IsSmoothForm β)
    (hp : M.pullback N f β = α) (x : M.Point)
    (hnd : M.Nondegenerate (M.exteriorDerivative α) x) :
    Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x) := by
  have hd := M.exteriorDerivative_pullback N ⟨f, hf⟩ β hβ
  change M.exteriorDerivative (M.pullback N f β) = M.pullback N f (N.exteriorDerivative β) at hd
  rw [hp] at hd
  have hi := M.injective_mfderiv_of_nondegenerate_pullback N f (N.exteriorDerivative β) x
    (by rw [← hd]; exact hnd)
  refine ⟨hi, ?_⟩
  subst e
  exact LinearMap.injective_iff_surjective.mp hi

/-- Primitive transport sends the form-determined source Liouville vector
to the form-determined target Liouville vector. Nondegeneracy is the
constructed symplecticity of the two actual primitives. -/
theorem map_liouvilleVector_of_primitive_pullback {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (hdim : d = e)
    (f : M.Point → N.Point)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f)
    (α : M.Form 1) (β : N.Form 1) (hβ : N.IsSmoothForm β)
    (hp : M.pullback N f β = α) (x : M.Point)
    (hndM : M.Nondegenerate (M.exteriorDerivative α) x)
    (hndN : N.Nondegenerate (N.exteriorDerivative β) (f x)) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x (M.liouvilleVector α x) =
      N.liouvilleVector β (f x) := by
  apply (N.liouvilleVector_eq β (f x) hndN ?_).symm
  intro w
  obtain ⟨v, rfl⟩ := (M.bijective_mfderiv_of_nondegenerate_primitive_pullback
    N hdim f hf α β hβ hp x hndM).2 w
  have hd := M.exteriorDerivative_pullback N ⟨f, hf⟩ β hβ
  change M.exteriorDerivative (M.pullback N f β) = M.pullback N f (N.exteriorDerivative β) at hd
  rw [hp] at hd
  have he := congrArg (fun η => η ![M.liouvilleVector α x, v]) (congrFun hd x)
  have hvec : (fun j : Fin 2 => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x
      (![M.liouvilleVector α x, v] j)) =
      ![mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x (M.liouvilleVector α x),
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x v] := by
    funext j
    fin_cases j <;> rfl
  change M.exteriorDerivative α x ![M.liouvilleVector α x, v] =
    N.exteriorDerivative β (f x) (fun j =>
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x (![M.liouvilleVector α x, v] j)) at he
  rw [hvec] at he
  have hz := M.liouvilleVector_contraction α x (M.liouvilleEquation_exists α x hndM) v
  have hpv := congrArg (fun η => η (fun _ => v)) (congrFun hp x)
  exact he.symm.trans (hz.trans hpv.symm)

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.CompleteLiouvilleManifold
open SmoothManifold

/-- Vertical primitive transport from a raw original completed slice to
an actual completed ambient transports its actual Liouville field. -/
theorem map_native_liouvilleVector_of_primitive_pullback {d e : ℕ}
    (Y : CompleteLiouvilleManifold e) (M : SmoothManifold d) (hdim : d = e)
    (f : M.Point → Y.manifold.Point)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f)
    (α : M.Form 1) (hp : M.pullback Y.manifold f Y.primitive = α)
    (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative α) x) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x (M.liouvilleVector α x) = Y.field (f x) := by
  rw [M.map_liouvilleVector_of_primitive_pullback Y.manifold hdim f hf α Y.primitive
    Y.smooth_primitive hp x hnd (Y.symplectic.2.2 _ (mem_univ _))]
  exact (Y.field_eq_liouvilleVector _).symm

end FsFltz.Geometry.CompleteLiouvilleManifold

namespace FsFltz.Geometry.PairDeformation
open SmoothManifold IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The proved vertical primitive equation of the original quotient family
transports its native Liouville field to the actual completed endpoint.
The map is the same quotient comparison followed by the same completion
presentation; no completed inverse or field equation is supplied. -/
theorem map_liouvilleVector_ambientNativeTotalMap
    (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
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
    (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Q.source.ambientCompletion.ambient.manifold.Point)
    (hq : letI := totalFamilyChartedSpace hδ C hzero hjoint
      ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ q)
    (htransport : ∀ t,
      (completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t)).pullback
        Q.source.ambientCompletion.ambient.manifold
        (q ∘ sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t)
        (Q.completedPrimitive t) = Λ t)
    (hΛnd : ∀ t x, (completionManifold hδ (C t) (hemb t) (hC t)
      (hboundary t) (hinv t) (hzero t)).Nondegenerate
      ((completionManifold hδ (C t) (hemb t) (hC t)
        (hboundary t) (hinv t) (hzero t)).exteriorDerivative (Λ t)) x)
    (t : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n))
      ((Q.ambientCompletionPresentation t).equiv ∘
        (q ∘ sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t)) x
      ((completionManifold hδ (C t) (hemb t) (hC t)
        (hboundary t) (hinv t) (hzero t)).liouvilleVector (Λ t) x) =
      (Q.pair t).ambientCompletion.ambient.field
        ((Q.ambientCompletionPresentation t).equiv
          (q (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t x))) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let X := completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t)
  let p := Q.ambientCompletionPresentation t
  let qs := q ∘ sliceIn c t
  have hqs : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ qs :=
    hq.comp (contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t)
  have hp : X.pullback (Q.pair t).ambientCompletion.ambient.manifold
      (p.equiv ∘ qs) (Q.pair t).ambientCompletion.ambient.primitive = Λ t := by
    rw [X.pullback_comp Q.source.ambientCompletion.ambient.manifold
      (Q.pair t).ambientCompletion.ambient.manifold
      (fun x => hqs.mdifferentiableAt (by simp))
      (fun x => p.equiv.contMDiff.mdifferentiableAt (by simp))]
    exact htransport t
  exact (Q.pair t).ambientCompletion.ambient.map_native_liouvilleVector_of_primitive_pullback
    X hdim (p.equiv ∘ qs) (p.equiv.contMDiff.comp hqs) (Λ t) hp x (hΛnd t x)

end FsFltz.Geometry.PairDeformation
