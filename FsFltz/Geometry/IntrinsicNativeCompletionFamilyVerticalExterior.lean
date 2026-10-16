import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVertical
import FsFltz.Geometry.FamilyLiouville

/-!
# The vertical exterior derivative on the original total atlas

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. The spatial exterior derivative of the same
primitive family has a smooth native total two-form extension. It is not
identified with the total exterior derivative of a parameterized extension.

This module proves native `ContMDiff ∞` regularity in the closed parameter
model. `IntrinsicNativeCompletionFamilyExteriorGerms` supplies real open
coefficient extensions of the same two-form on covering original patches.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology Bundle

namespace FsFltz.Geometry.SmoothManifold

/-- Joint form coefficients have a jointly smooth spatial exterior
derivative on the same actual open extension neighborhoods. -/
theorem IsSmoothFormFamily.exteriorDerivative {d r : ℕ}
    {N : SmoothManifold d} {α : ℝ → N.Form r} (hα : N.IsSmoothFormFamily α) :
    N.IsSmoothFormFamily (fun t => N.exteriorDerivative (α t)) := by
  intro a
  obtain ⟨U, hU, hcover, hcoeff⟩ := hα a
  let V := U ∩ (univ ×ˢ (chartAt (Model d) a).target)
  have hV : IsOpen V := hU.inter (isOpen_univ.prod (chartAt (Model d) a).open_target)
  refine ⟨V, hV, subset_inter hcover (Set.prod_mono (subset_univ _) Subset.rfl), ?_⟩
  apply (contDiffOn_spatialExtDeriv
    (fun p : ℝ × Model d => N.formInChart a (α p.1) p.2) U hU hcoeff).mono
      inter_subset_left |>.congr
  intro p hp
  have hs := (hcoeff.contDiffAt (hU.mem_nhds hp.1)).comp p.2
    (contDiffAt_const.prodMk contDiffAt_id)
  exact N.formInChart_exteriorDerivative_of_contDiffAt (α p.1) a p.2 hp.2.2 hs

/-- Taking the actual spatial exterior derivative preserves the existing
interval family contract, with its explicit real coefficient extensions. -/
theorem IsSmoothIntervalFormFamily.exteriorDerivative {d r : ℕ}
    {N : SmoothManifold d} {α : Parameter → N.Form r}
    (hα : N.IsSmoothIntervalFormFamily α) :
    N.IsSmoothIntervalFormFamily (fun t => N.exteriorDerivative (α t)) := by
  obtain ⟨β, hβ, heq⟩ := hα
  refine ⟨fun t => N.exteriorDerivative (β t), hβ.exteriorDerivative, ?_⟩
  intro t
  dsimp only
  rw [heq t]

/-- Every actual interval slice of a smooth form family is a smooth form. -/
theorem IsSmoothIntervalFormFamily.slice {d r : ℕ} {N : SmoothManifold d}
    {α : Parameter → N.Form r} (hα : N.IsSmoothIntervalFormFamily α) (t : Parameter) :
    N.IsSmoothForm (α t) := by
  obtain ⟨β, hβ, heq⟩ := hα
  rw [← heq t]
  intro a y hy
  obtain ⟨U, hU, hcover, hcoeff⟩ := hβ a
  have hmem : (t.val, y) ∈ U := hcover ⟨t.property, hy⟩
  exact ((hcoeff.contDiffAt (hU.mem_nhds hmem)).comp y
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

end FsFltz.Geometry.SmoothManifold


namespace FsFltz.Geometry

section TangentPair

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  (I : ModelWithCorners ℝ E H) [ChartedSpace H X]

/-- Two actual tangent vectors at the same base point, with the native
direct-sum vector-bundle topology and atlas. -/
abbrev TangentPairBundle := Bundle.TotalSpace (E × E)
  (TangentSpace I (M := X) ×ᵇ TangentSpace I (M := X))

variable [IsManifold I ∞ X]

/-- Projection onto the first native tangent vector is smooth. -/
theorem contMDiff_tangentPair_fst :
    ContMDiff (I.prod 𝓘(ℝ, E × E)) I.tangent ∞
      (fun v : TangentPairBundle I (X := X) =>
        (⟨v.proj, v.2.1⟩ : TangentBundle I X)) := by
  intro v
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨(Bundle.contMDiff_proj (TangentSpace I ×ᵇ TangentSpace I)).contMDiffAt, ?_⟩
  let e₂ := trivializationAt (E × E)
    (TangentSpace I (M := X) ×ᵇ TangentSpace I (M := X)) v.proj
  have hv : v ∈ e₂.source := FiberBundle.mem_trivializationAt_proj_source
  have he : ContMDiffAt (I.prod 𝓘(ℝ, E × E)) (I.prod 𝓘(ℝ, E × E)) ∞ e₂ v :=
    e₂.contMDiffOn.contMDiffAt (e₂.open_source.mem_nhds hv)
  have h := (ContinuousLinearMap.fst ℝ E E).contDiff.contMDiff.contMDiffAt.comp v
    (contMDiffAt_snd.comp v he)
  convert h using 1
  funext w
  rfl

/-- Projection onto the second native tangent vector is smooth. -/
theorem contMDiff_tangentPair_snd :
    ContMDiff (I.prod 𝓘(ℝ, E × E)) I.tangent ∞
      (fun v : TangentPairBundle I (X := X) =>
        (⟨v.proj, v.2.2⟩ : TangentBundle I X)) := by
  intro v
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨(Bundle.contMDiff_proj (TangentSpace I ×ᵇ TangentSpace I)).contMDiffAt, ?_⟩
  let e₂ := trivializationAt (E × E)
    (TangentSpace I (M := X) ×ᵇ TangentSpace I (M := X)) v.proj
  have hv : v ∈ e₂.source := FiberBundle.mem_trivializationAt_proj_source
  have he : ContMDiffAt (I.prod 𝓘(ℝ, E × E)) (I.prod 𝓘(ℝ, E × E)) ∞ e₂ v :=
    e₂.contMDiffOn.contMDiffAt (e₂.open_source.mem_nhds hv)
  have h := (ContinuousLinearMap.snd ℝ E E).contDiff.contMDiff.contMDiffAt.comp v
    (contMDiffAt_snd.comp v he)
  convert h using 1
  funext w
  rfl

/-- Two smooth native tangent maps over the same base make a smooth map
into the direct-sum bundle; this uses the actual bundle trivializations. -/
theorem contMDiff_tangentPair_mk
    {F G S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace S] (J : ModelWithCorners ℝ F G)
    [ChartedSpace G S]
    (f : S → X) (u v : (s : S) → TangentSpace I (f s))
    (hu : ContMDiff J I.tangent ∞ (fun s => (⟨f s, u s⟩ : TangentBundle I X)))
    (hv : ContMDiff J I.tangent ∞ (fun s => (⟨f s, v s⟩ : TangentBundle I X))) :
    ContMDiff J (I.prod 𝓘(ℝ, E × E)) ∞
      (fun s => (⟨f s, (u s, v s)⟩ : TangentPairBundle I (X := X))) := by
  intro s
  rw [Bundle.contMDiffAt_totalSpace]
  have hu' := Bundle.contMDiffAt_totalSpace.mp (hu s)
  have hv' := Bundle.contMDiffAt_totalSpace.mp (hv s)
  exact ⟨hu'.1, hu'.2.prodMk_space hv'.2⟩

/-- The actual differential acts smoothly on two tangent vectors at the
same point of the original manifold. -/
theorem contMDiff_tangentPairMap {d : ℕ} {N : SmoothManifold d} {f : X → N.Point}
    (hf : ContMDiff I 𝓘(ℝ, Model d) ∞ f) :
    ContMDiff (I.prod 𝓘(ℝ, E × E))
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d × Model d)) ∞
      (fun v : TangentPairBundle I (X := X) =>
        (⟨f v.proj, (mfderiv I 𝓘(ℝ, Model d) f v.proj v.2.1,
          mfderiv I 𝓘(ℝ, Model d) f v.proj v.2.2)⟩ :
            TangentPairBundle 𝓘(ℝ, Model d) (X := N.Point))) := by
  exact contMDiff_tangentPair_mk 𝓘(ℝ, Model d) (I.prod 𝓘(ℝ, E × E))
    (fun v : TangentPairBundle I (X := X) => f v.proj)
    (fun v => mfderiv I 𝓘(ℝ, Model d) f v.proj v.2.1)
    (fun v => mfderiv I 𝓘(ℝ, Model d) f v.proj v.2.2)
    ((hf.contMDiff_tangentMap (by simp)).comp (contMDiff_tangentPair_fst I))
    ((hf.contMDiff_tangentMap (by simp)).comp (contMDiff_tangentPair_snd I))

end TangentPair

end FsFltz.Geometry

namespace FsFltz.Geometry.SmoothManifold

/-- The jointly smooth two-form family has smooth evaluation on the native
bundle of two spatial tangent vectors sharing their actual base point. -/
theorem IsSmoothIntervalFormFamily.contMDiff_tangentPairEvaluation
    {d : ℕ} {N : SmoothManifold d} {α : Parameter → N.Form 2}
    (hα : N.IsSmoothIntervalFormFamily α) :
    ContMDiff ((𝓡∂ 1).prod
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d × Model d))) 𝓘(ℝ, ℝ) ∞
      (fun p : Parameter × TangentPairBundle 𝓘(ℝ, Model d) (X := N.Point) =>
        α p.1 p.2.proj ![p.2.2.1, p.2.2.2]) := by
  obtain ⟨β, hβ, heq⟩ := hα
  intro p
  let x := p.2.proj
  let c := chartAt (Model d) x
  let e₂ := trivializationAt (Model d × Model d)
    (TangentSpace 𝓘(ℝ, Model d) (M := N.Point) ×ᵇ
      TangentSpace 𝓘(ℝ, Model d) (M := N.Point)) x
  have hx : x ∈ c.source := mem_chart_source _ _
  have he : p.2 ∈ e₂.source := FiberBundle.mem_trivializationAt_proj_source
  have hs₂ : ContMDiffAt ((𝓡∂ 1).prod
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d × Model d)))
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d × Model d)) ∞
      (fun q : Parameter × TangentPairBundle 𝓘(ℝ, Model d) (X := N.Point) => e₂ q.2) p :=
    (e₂.contMDiffOn.contMDiffAt (e₂.open_source.mem_nhds he)).comp p contMDiffAt_snd
  have hvec := contMDiffAt_snd.comp p hs₂
  have hv₁ := (ContinuousLinearMap.fst ℝ (Model d) (Model d)).contDiff.contMDiff.contMDiffAt.comp p hvec
  have hv₂ := (ContinuousLinearMap.snd ℝ (Model d) (Model d)).contDiff.contMDiff.contMDiffAt.comp p hvec
  have hproj : ContMDiff ((𝓡∂ 1).prod
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d × Model d))) 𝓘(ℝ, Model d) ∞
      (fun q : Parameter × TangentPairBundle 𝓘(ℝ, Model d) (X := N.Point) => q.2.proj) :=
    (Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, Model d) (M := N.Point) ×ᵇ
      TangentSpace 𝓘(ℝ, Model d) (M := N.Point))).comp contMDiff_snd
  have hbase := ((contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := x)).contMDiffAt
      (c.open_source.mem_nhds hx)).comp p (hproj p)
  have ht : ContMDiffAt ((𝓡∂ 1).prod
      ((𝓘(ℝ, Model d)).prod 𝓘(ℝ, Model d × Model d))) 𝓘(ℝ, ℝ) ∞
      (fun q : Parameter × TangentPairBundle 𝓘(ℝ, Model d) (X := N.Point) => q.1.val) p :=
    contMDiff_subtypeVal_Icc.contMDiffAt.comp p contMDiffAt_fst
  obtain ⟨U, hU, hcover, hcoeff⟩ := hβ x
  have hpU : (p.1.val, c x) ∈ U := hcover ⟨p.1.property, c.map_source hx⟩
  have hc := (hcoeff.contDiffAt (hU.mem_nhds hpU)).contMDiffAt.comp p
    (ht.prodMk_space hbase)
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hcurSmooth : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Model d)
        (F := ℝ) (n := 1)).toContinuousLinearMap
  have hcur := hcurSmooth.contMDiff.contMDiffAt.comp p hc
  have hs := (L.symm.contDiff.contMDiff.contMDiffAt.comp p (hcur.clm_apply hv₁)).clm_apply hv₂
  apply hs.congr_of_eventuallyEq
  have hn : ∀ᶠ q in 𝓝 p, q.2.proj ∈ c.source :=
    hproj.continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx)
  filter_upwards [hn] with q hq
  dsimp only [Function.comp_def]
  rw [heq q.1]
  let e := trivializationAt (Model d) (TangentSpace 𝓘(ℝ, Model d)) x
  have hvec' : (e₂ q.2).2 =
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.1,
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.2) := by
    have he₁ : (e (⟨q.2.proj, q.2.2.1⟩ : TangentBundle 𝓘(ℝ, Model d) N.Point)).2 =
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.1 := by
      rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hq,
        TangentBundle.continuousLinearMapAt_trivializationAt hq]
      rfl
    have he₂ : (e (⟨q.2.proj, q.2.2.2⟩ : TangentBundle 𝓘(ℝ, Model d) N.Point)).2 =
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.2 := by
      rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hq,
        TangentBundle.continuousLinearMapAt_trivializationAt hq]
      rfl
    exact Prod.ext he₁ he₂
  rw [hvec']
  change α q.1 q.2.proj ![q.2.2.1, q.2.2.2] =
    N.formInChart x (α q.1) (c q.2.proj)
      (Matrix.vecCons (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.1)
        (fun _ : Fin 1 => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.2))
  have htuple : Matrix.vecCons
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.1)
      (fun _ : Fin 1 => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.2) =
        ![mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.1,
          mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.2] := by
    ext j
    fin_cases j <;> rfl
  rw [htuple]
  dsimp only [formInChart]
  rw [c.left_inv hq]
  have hd := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm_comp_deriv hq
  change α q.1 q.2.proj ![q.2.2.1, q.2.2.2] = α q.1 q.2.proj (fun j =>
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c q.2.proj)
      (![mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.1,
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2.2] j))
  apply congrArg (α q.1 q.2.proj)
  funext j
  fin_cases j
  · exact (congrArg (fun A => A q.2.2.1) hd).symm
  · exact (congrArg (fun A => A q.2.2.2) hd).symm

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry

section NativeTwoForms

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  (I : ModelWithCorners ℝ E H) [ChartedSpace H X]

/-- An actual total two-form extending spatial two-forms through the same
native total map. Parameter components are allowed. -/
def nativeTotalTwoForm {d : ℕ} (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (η : Parameter → N.Form 2) :
    (z : X) → TangentSpace I z [⋀^Fin 2]→L[ℝ] ℝ := fun z =>
  (η (p z) (q z)).compContinuousLinearMap (mfderiv I 𝓘(ℝ, Model d) q z)

variable [IsManifold I ∞ X]

/-- The native total two-form has smooth scalar evaluation on the actual
tangent-pair direct-sum bundle of the original total manifold. -/
theorem contMDiff_nativeTotalTwoForm_eval {d : ℕ} (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (η : Parameter → N.Form 2)
    (hp : ContMDiff I (𝓡∂ 1) ∞ p)
    (hq : ContMDiff I 𝓘(ℝ, Model d) ∞ q)
    (hη : N.IsSmoothIntervalFormFamily η) :
    ContMDiff (I.prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞
      (fun v : TangentPairBundle I (X := X) =>
        nativeTotalTwoForm I N p q η v.proj ![v.2.1, v.2.2]) := by
  have hp' : ContMDiff (I.prod 𝓘(ℝ, E × E)) (𝓡∂ 1) ∞
      (fun v : TangentPairBundle I (X := X) => p v.proj) :=
    hp.comp (Bundle.contMDiff_proj (TangentSpace I (M := X) ×ᵇ TangentSpace I (M := X)))
  have h := hη.contMDiff_tangentPairEvaluation.comp (hp'.prodMk (contMDiff_tangentPairMap I hq))
  convert h using 1
  funext v
  apply congrArg (η (p v.proj) (q v.proj))
  funext j
  fin_cases j <;> rfl

omit [IsManifold I ∞ X] in
/-- Restricting the total two-form to an actual spatial slice is the
literal spatial pullback, by the chain rule for that exact inclusion. -/
theorem nativeTotalTwoForm_restrict {a d : ℕ}
    (M : SmoothManifold a) (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (η : Parameter → N.Form 2)
    (hq : ContMDiff I 𝓘(ℝ, Model d) ∞ q)
    (i : M.Point → X) (hi : ContMDiff 𝓘(ℝ, Model a) I ∞ i)
    (t : Parameter) (hp : ∀ x, p (i x) = t) (x : M.Point) :
    (nativeTotalTwoForm I N p q η (i x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model a) I i x) = M.pullback N (q ∘ i) (η t) x := by
  rw [nativeTotalTwoForm, hp x]
  have hd := mfderiv_comp x (hq.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  ext vs
  change η t (q (i x)) (fun j =>
      mfderiv I 𝓘(ℝ, Model d) q (i x)
        (mfderiv 𝓘(ℝ, Model a) I i x (vs j))) =
    η t (q (i x)) (fun j => mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model d) (q ∘ i) x (vs j))
  rw [hd]
  rfl

end NativeTwoForms

end FsFltz.Geometry

namespace FsFltz.Geometry.PairDeformation
open IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (Q : PairDeformation n)
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
  (hzero : ∀ t x, C t (0, x) = x.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (Λ : ∀ t, (completionManifold hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t)).Form 1)
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    Q.source.ambientCompletion.ambient.manifold.Point)
  (hq : letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ q)
  (htransport : ∀ t, (completionManifold hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t)).pullback Q.source.ambientCompletion.ambient.manifold
    (q ∘ sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t)
    (Q.completedPrimitive t) = Λ t)

include hboundary hmix hq htransport in
/-- The vertical exterior derivatives of the exact original primitives
have the canonical smooth actual total two-form extension on their original
atlas. Naming the witness transparently allows its real endpoint coefficient
extensions to refer to exactly this same two-form.
The native tangent-pair bundle checks both vectors at the same point.
Spatial naturality identifies every restriction with `d Λ_t`; no extra
derivative-transport or completed-regularity hypothesis is required. -/
theorem ambientNativeTotalTwoForm_extension :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    letI := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    let Ξ := nativeTotalTwoForm (familyModel (k + 1))
      Q.source.ambientCompletion.ambient.manifold (parameter c) q
      (fun t => Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive t))
    ContMDiff ((familyModel (k + 1)).prod
        𝓘(ℝ, (Model 1 × Model (k + 1)) × (Model 1 × Model (k + 1)))) 𝓘(ℝ, ℝ) ∞
        (fun v : TangentPairBundle (familyModel (k + 1))
            (X := TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) =>
          Ξ v.proj ![v.2.1, v.2.2]) ∧
      ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
        ∀ x, (Ξ (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t) x) =
              (completionManifold hδ (C t) (hemb t) (hC t)
                (hboundary t) (hinv t) (hzero t)).exteriorDerivative (Λ t) x := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let N := Q.source.ambientCompletion.ambient.manifold
  let η := fun t => N.exteriorDerivative (Q.completedPrimitive t)
  let Ξ := nativeTotalTwoForm (familyModel (k + 1)) N (parameter c) q η
  refine ⟨contMDiff_nativeTotalTwoForm_eval (familyModel (k + 1)) N
    (parameter c) q η (contMDiff_parameter hδ C hboundary hzero hjoint hmix) hq
      Q.completedAmbientPrimitive_smooth.exteriorDerivative, ?_⟩
  intro t
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let X := completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t)
  have hi := contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t
  have hqs := hq.comp hi
  have hd := X.exteriorDerivative_pullback N ⟨q ∘ sliceIn c t, hqs⟩
    (Q.completedPrimitive t) (Q.completedAmbientPrimitive_smooth.slice t)
  change X.exteriorDerivative (X.pullback N (q ∘ sliceIn c t) (Q.completedPrimitive t)) =
    X.pullback N (q ∘ sliceIn c t) (η t) at hd
  rw [htransport t] at hd
  intro x
  rw [nativeTotalTwoForm_restrict (familyModel (k + 1)) X N (parameter c) q η hq
    (sliceIn c t) hi t (parameter_sliceIn c t) x]
  exact (congrFun hd x).symm


include hboundary hmix hq htransport in
/-- The vertical exterior derivatives of the exact original primitives
have a smooth actual total two-form extension on their original atlas.
The native tangent-pair bundle checks both vectors at the same point.
Spatial naturality identifies every restriction with `d Λ_t`; no extra
derivative-transport or completed-regularity hypothesis is required. -/
theorem exists_ambientNativeTotalTwoForm_extension :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    letI := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
    ∃ Ξ : (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) →
        TangentSpace (familyModel (k + 1)) z [⋀^Fin 2]→L[ℝ] ℝ,
      ContMDiff ((familyModel (k + 1)).prod
        𝓘(ℝ, (Model 1 × Model (k + 1)) × (Model 1 × Model (k + 1)))) 𝓘(ℝ, ℝ) ∞
        (fun v : TangentPairBundle (familyModel (k + 1))
            (X := TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) =>
          Ξ v.proj ![v.2.1, v.2.2]) ∧
      ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
        ∀ x, (Ξ (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t) x) =
              (completionManifold hδ (C t) (hemb t) (hC t)
                (hboundary t) (hinv t) (hzero t)).exteriorDerivative (Λ t) x := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let N := Q.source.ambientCompletion.ambient.manifold
  let Ξ := nativeTotalTwoForm (familyModel (k + 1)) N (parameter c) q
    (fun t => N.exteriorDerivative (Q.completedPrimitive t))
  exact ⟨Ξ, Q.ambientNativeTotalTwoForm_extension hδ C hemb hC hboundary hinv
    hzero hjoint hmix Λ q hq htransport⟩

end FsFltz.Geometry.PairDeformation
