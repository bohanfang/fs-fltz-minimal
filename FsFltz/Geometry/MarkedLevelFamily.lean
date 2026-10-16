import FsFltz.Geometry.RegularFiberManifold

/-!
# Local smooth motions of actual parameterized marked levels

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009;
`geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and `sec:lean`,
lines 788–814. A surjective spatial differential gives a joint normal form
whose first coordinates are the actual parameter and the actual marked
level functions. The resulting local motions are smooth jointly and preserve
those functions literally. No compact global trivialization is an input or
a conclusion of this local construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A nonzero covector on the kernel supplies the extra marked-boundary
coordinate without destroying the already surjective level coordinates. -/
theorem surjective_prod_of_nonzero_on_kernel (L : E →L[ℝ] F)
    (r : E →L[ℝ] ℝ) (hL : Function.Surjective L)
    (z : E) (hz : L z = 0) (hrz : r z ≠ 0) :
    Function.Surjective (L.prod r) := by
  rintro ⟨c, a⟩
  obtain ⟨v, hv⟩ := hL c
  refine ⟨v + ((a - r v) / r z) • z, ?_⟩
  apply Prod.ext
  · simp [hv, hz]
  · change r (v + ((a - r v) / r z) • z) = a
    simp only [map_add, map_smul, smul_eq_mul]
    field_simp
    ring

/-- Spatial surjectivity gives surjectivity after retaining the time
coordinate, irrespective of the time derivative of the equations. -/
theorem surjective_parameter_prod (D : (ℝ × E) →L[ℝ] F)
    (hD : Function.Surjective (D.comp (ContinuousLinearMap.inr ℝ ℝ E))) :
    Function.Surjective ((ContinuousLinearMap.fst ℝ ℝ E).prod D) := by
  rintro ⟨t, c⟩
  obtain ⟨v, hv⟩ := hD (c - D (t, 0))
  refine ⟨(t, v), ?_⟩
  apply Prod.ext
  · rfl
  · have he : (t, v) = (t, 0) + (0, v) := by simp
    change D (t, v) = c
    rw [he, map_add]
    change D (t, 0) + D.comp (ContinuousLinearMap.inr ℝ ℝ E) v = c
    rw [hv]
    abel

end Linear

section LocalNormalForm

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Joint normal forms retain the actual time and level functions.
The hypothesis concerns the actual spatial slice at the specified point. -/
theorem exists_parameter_level_kernel_normalForm {f : ℝ × M → F} {a : ℝ × M}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ f)
    (hd : Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x => f (a.1, x)) a.2)) :
    letI : ChartedSpace (ℝ × E) (ℝ × M) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ E) (ℝ × M))
    let g : ℝ × M → ℝ × F := fun p => (p.1, f p)
    let D : (ℝ × E) →L[ℝ] (ℝ × F) := mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g a
    ∃ e : PartialDiffeomorph 𝓘(ℝ, ℝ × E)
        𝓘(ℝ, (ℝ × F) × D.ker) (ℝ × M) ((ℝ × F) × D.ker) ∞,
      a ∈ e.source ∧ ∀ p ∈ e.source, (e p).1 = (p.1, f p) := by
  let : ChartedSpace (ℝ × E) (ℝ × M) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ E) (ℝ × M))
  let : IsManifold 𝓘(ℝ, ℝ × E) ∞ (ℝ × M) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (ℝ × M))
  let g : ℝ × M → ℝ × F := fun p => (p.1, f p)
  have hf' : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) ∞ f := by
    simpa only [modelWithCornersSelf_prod] using hf
  have hg : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ g := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst.prodMk_space hf
  have hin : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) ∞
      (fun x : M => (a.1, x)) := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_const.prodMk contMDiff_id :
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (fun x : M => (a.1, x)))
  have hdin : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) (fun x : M => (a.1, x)) a.2 =
      ContinuousLinearMap.inr ℝ ℝ E := by
    rw [modelWithCornersSelf_prod]
    have h := mfderiv_prodMk (x := a.2)
      (mdifferentiableAt_const (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) (c := a.1))
      (mdifferentiableAt_id (I := 𝓘(ℝ, E)))
    rw [mfderiv_const, mfderiv_id] at h
    convert h using 1 <;> rfl
  have hslice : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x => f (a.1, x)) a.2 =
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) f a).comp
        (ContinuousLinearMap.inr ℝ ℝ E) := by
    rw [show (fun x => f (a.1, x)) = f ∘ (fun x => (a.1, x)) from rfl,
      mfderiv_comp a.2 (hf'.mdifferentiableAt (by simp)) (hin.mdifferentiableAt (by simp)),
      hdin]
  have hsurj : Function.Surjective (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g a) := by
    have hfst : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (Prod.fst : ℝ × M → ℝ) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    have hder : mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g a =
        (ContinuousLinearMap.fst ℝ ℝ E).prod
          (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) f a) := by
      have hfst' : mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ)
          (Prod.fst : ℝ × M → ℝ) a = ContinuousLinearMap.fst ℝ ℝ E := by
        convert (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (x := a)) using 1 <;> rfl
      have hprod : mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g a =
          (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × M → ℝ) a).prod
            (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) f a) := by
        have h₁ := (hfst.mdifferentiableAt (x := a) (by simp)).hasMFDerivAt
        have h₂ := (hf'.mdifferentiableAt (x := a) (by simp)).hasMFDerivAt
        have h : HasMFDerivAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g a
            ((mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × M → ℝ) a).prod
              (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) f a)) :=
          ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩
        exact h.mfderiv
      rw [hprod, hfst']
    rw [hder]
    exact surjective_parameter_prod (E := E) (F := F)
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) f a : (ℝ × E) →L[ℝ] F)
      (by rwa [← hslice])
  exact exists_regularLevel_kernel_normalForm hg hsurj

end LocalNormalForm

section LocalMotion

variable {E F K Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [TopologicalSpace Q] [ChartedSpace E Q]

/-- Translation of the parameter coordinate in an actual smooth normal
form gives a jointly smooth local motion, identity at zero time, preserving
every marked equation exactly. Its domain is genuinely open, so it also
extends beyond the original interval endpoints. -/
theorem exists_local_parameter_motion
    (τ : Q → ℝ) (f : Q → F)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, (ℝ × F) × K) Q ((ℝ × F) × K) ∞)
    (he : ∀ x ∈ e.source, (e x).1 = (τ x, f x))
    (a : Q) (ha : a ∈ e.source) :
    ∃ (U : Set (ℝ × Q)) (Ψ : ℝ × Q → Q),
      IsOpen U ∧ (0, a) ∈ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Ψ U ∧
      (∀ x, (0, x) ∈ U → Ψ (0, x) = x) ∧
      ∀ p ∈ U, Ψ p ∈ e.source ∧ τ (Ψ p) = τ p.2 + p.1 ∧ f (Ψ p) = f p.2 := by
  let S : Set (ℝ × Q) := univ ×ˢ e.source
  let T : ℝ × ((ℝ × F) × K) → ((ℝ × F) × K) :=
    fun p => ((p.2.1.1 + p.1, p.2.1.2), p.2.2)
  have hT : ContDiff ℝ ∞ T := by
    dsimp [T]
    fun_prop
  let q : ℝ × Q → ((ℝ × F) × K) := fun p => T (p.1, e p.2)
  have hS : IsOpen S := isOpen_univ.prod e.open_source
  have heS : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      𝓘(ℝ, (ℝ × F) × K) ∞ (fun p : ℝ × Q => e p.2) S :=
    e.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn (fun p hp => hp.2)
  have hq : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      𝓘(ℝ, (ℝ × F) × K) ∞ q S :=
    hT.contMDiff.comp_contMDiffOn (contMDiff_fst.contMDiffOn.prodMk_space heS)
  let U : Set (ℝ × Q) := S ∩ q ⁻¹' e.target
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage hS e.open_target
  have hqzero (x : Q) : q (0, x) = e x := by
    dsimp [q, T]
    simp only [add_zero, Prod.mk.eta]
  let Ψ : ℝ × Q → Q := e.symm ∘ q
  have hΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Ψ U :=
    e.contMDiffOn_invFun.comp (hq.mono inter_subset_left) (fun p hp => hp.2)
  refine ⟨U, Ψ, hU, ⟨⟨mem_univ _, ha⟩, ?_⟩, hΨ, ?_, ?_⟩
  · rw [mem_preimage, hqzero]
    exact e.toOpenPartialHomeomorph.map_source ha
  · intro x hx
    change e.symm (q (0, x)) = x
    rw [hqzero]
    exact e.toOpenPartialHomeomorph.left_inv hx.1.2
  · intro p hp
    have hsrc : Ψ p ∈ e.source := e.toOpenPartialHomeomorph.map_target hp.2
    have hcoord : e (Ψ p) = q p := e.toOpenPartialHomeomorph.right_inv hp.2
    refine ⟨hsrc, ?_, ?_⟩
    · have h := congrArg (fun z : ((ℝ × F) × K) => z.1.1) hcoord
      change (e (Ψ p)).1.1 = (e p.2).1.1 + p.1 at h
      rw [he (Ψ p) hsrc, he p.2 hp.1.2] at h
      exact h
    · have h := congrArg (fun z : ((ℝ × F) × K) => z.1.2) hcoord
      change (e (Ψ p)).1.2 = (e p.2).1.2 at h
      rw [he (Ψ p) hsrc, he p.2 hp.1.2] at h
      exact h

end LocalMotion

section ParameterMotion

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual level equations with surjective spatial differential produce
the local motion directly, rather than consuming an assumed family atlas. -/
theorem exists_parameter_level_local_motion {f : ℝ × M → F} {a : ℝ × M}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ f)
    (hd : Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x => f (a.1, x)) a.2)) :
    letI : ChartedSpace (ℝ × E) (ℝ × M) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ E) (ℝ × M))
    ∃ (U : Set (ℝ × (ℝ × M))) (Ψ : ℝ × (ℝ × M) → ℝ × M),
      IsOpen U ∧ (0, a) ∈ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × E)) 𝓘(ℝ, ℝ × E) ∞ Ψ U ∧
      (∀ x, (0, x) ∈ U → Ψ (0, x) = x) ∧
      ∀ p ∈ U, (Ψ p).1 = p.2.1 + p.1 ∧ f (Ψ p) = f p.2 := by
  let : ChartedSpace (ℝ × E) (ℝ × M) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ E) (ℝ × M))
  obtain ⟨e, ha, he⟩ := exists_parameter_level_kernel_normalForm hf hd
  obtain ⟨U, Ψ, hU, haU, hΨ, hzero, hpres⟩ :=
    exists_local_parameter_motion Prod.fst f e he a ha
  refine ⟨U, Ψ, hU, haU, hΨ, hzero, fun p hp => ?_⟩
  exact (hpres p hp).2

end ParameterMotion

section NativeMarkedRegularity

variable {d k : ℕ} (M : SmoothManifold d) (N : SmoothManifold k)

/-- The positive derivative of a truncation function along an actual
fiber tangent supplies the third independent equation at ribbon boundary.
The conclusion uses the original ambient level and potential functions. -/
theorem surjective_markedLevel_of_fiber_tangent
    (f : M.Point → ℂ) (ρ : M.Point → ℝ)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (j : N.SmoothEmbedding M) (w : ℂ) (hj : ∀ x, f (j.map x) = w)
    (x : N.Point) (hreg : Function.Surjective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) f (j.map x)))
    (v : N.Tangent x)
    (hpos : N.scalarDerivative (ρ ∘ j.map) x v ≠ 0) :
    Function.Surjective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ × ℝ)
      (fun y => (f y, ρ y)) (j.map x)) := by
  let D : Model k →L[ℝ] Model d := mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model d) j.map x
  let L : Model d →L[ℝ] ℂ := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) f (j.map x)
  let r : Model d →L[ℝ] ℝ := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ (j.map x)
  have hfj : f ∘ j.map = fun _ => w := funext hj
  have hcompf := mfderiv_comp x (hf.mdifferentiableAt (by simp))
    (j.map.contMDiff.mdifferentiableAt (by simp))
  rw [hfj, mfderiv_const] at hcompf
  have hz : L (D v) = 0 := by
    exact (congrArg (fun A : Model k →L[ℝ] ℂ => A v) hcompf).symm
  have hcompr := mfderiv_comp x (hρ.mdifferentiableAt (by simp))
    (j.map.contMDiff.mdifferentiableAt (by simp))
  have hrz : r (D v) ≠ 0 := by
    unfold SmoothManifold.scalarDerivative at hpos
    rw [hcompr] at hpos
    exact hpos
  have hsurj := surjective_prod_of_nonzero_on_kernel (E := Model d) (F := ℂ)
    L r hreg (D v) hz hrz
  have h₁ := (hf.mdifferentiableAt (x := j.map x) (by simp)).hasMFDerivAt
  have h₂ := (hρ.mdifferentiableAt (x := j.map x) (by simp)).hasMFDerivAt
  have hpair : HasMFDerivAt 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ × ℝ)
      (fun y => (f y, ρ y)) (j.map x) (L.prod r) :=
    ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩
  rwa [hpair.mfderiv]

end NativeMarkedRegularity

end FsFltz.Geometry
