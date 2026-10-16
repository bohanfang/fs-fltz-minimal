import FsFltz.Geometry.SmoothScalarExtension
import FsFltz.Geometry.ImmersionNeighborhood

/-!
# Scalar extension from the actual compact hitting graph

Source: `geometric-part-fsf-proof.tex`, `eq:hittingprimitive` and
`eq:ribbonprimitive`, lines 1818–1875. Local projected inverses of the
actual immersed compact graph supply scalar germs; partition of unity
extends them globally. No witness extension is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

variable {E F X Y : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
  [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold 𝓘(ℝ, F) ∞ Y]

theorem exists_localLeftInverse_of_embedding
    {j : X → Y} (hj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ j)
    (hemb : Topology.IsEmbedding j)
    (himm : ∀ a, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) j a)) (a : X) :
    ∃ U : TopologicalSpace.Opens Y, j a ∈ U ∧
      ∃ g : U → X, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ g ∧
        ∀ y (hy : j y ∈ U), g ⟨j y, hy⟩ = y := by
  let c := chartAt F (j a)
  let J : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) j a
  obtain ⟨A, hA⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := J) (himm a)
  let p : Y → E := A ∘ c
  let h : X → E := p ∘ j
  let V : Set X := j ⁻¹' c.source
  have hV : IsOpen V := c.open_source.preimage hj.continuous
  have haV : a ∈ V := mem_chart_source _ _
  have hcs : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ c c.source := contMDiffOn_chart
  have hAs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ A := A.contDiff.contMDiff
  have hps : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ p c.source :=
    hAs.comp_contMDiffOn hcs
  have hhs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h V :=
    hps.comp hj.contMDiffOn (fun _ hy => hy)
  have hca := (hcs.contMDiffAt (c.open_source.mem_nhds haV)).mdifferentiableAt (by simp)
  have hia := hj.mdifferentiableAt (x := a) (by simp)
  have hcder : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c (j a) = ContinuousLinearMap.id ℝ F :=
    mfderiv_extChartAt_self
  have hhd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h a = ContinuousLinearMap.id ℝ E := by
    change mfderiv _ _ (A ∘ (c ∘ j)) a = _
    rw [mfderiv_comp a (hAs.mdifferentiableAt (by simp)) (hca.comp a hia),
      mfderiv_eq_fderiv, A.fderiv, mfderiv_comp a hca hia, hcder]
    ext v
    exact hA v
  obtain ⟨q, haq, heq⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    hV hhs haV (by rw [hhd]; exact Function.bijective_id)
  obtain ⟨S, hS, hSq⟩ := hemb.isInducing.isOpen_iff.mp q.open_source
  let U : TopologicalSpace.Opens Y :=
    ⟨S ∩ (c.source ∩ p ⁻¹' q.target),
      hS.inter (hps.continuousOn.isOpen_inter_preimage c.open_source q.open_target)⟩
  have haU : j a ∈ U := by
    refine ⟨?_, haV, ?_⟩
    · have h : a ∈ j ⁻¹' S := by rwa [hSq]
      exact h
    · change h a ∈ q.target
      rw [heq haq]
      exact q.map_source haq
  let g : U → X := fun x => q.symm (p x.val)
  have hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ g := by
    intro x
    exact (q.contMDiffOn_invFun.contMDiffAt (q.open_target.mem_nhds x.property.2.2)).comp x
      ((hps.contMDiffAt (c.open_source.mem_nhds x.property.2.1)).comp x
        contMDiff_subtype_val.contMDiffAt)
  refine ⟨U, haU, g, hg, ?_⟩
  intro y hy
  have hyq : y ∈ q.source := by
    rw [← hSq]
    exact hy.1
  change q.symm (h y) = y
  rw [heq hyq]
  exact q.left_inv hyq

/-- Smoothness of a map into an embedded submanifold follows from its
actual ambient composition. Local smooth left inverses supply the lift. -/
theorem contMDiff_of_comp_embedding
    {D Z : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace Z] [ChartedSpace D Z]
    {i : X → Y} (hi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ i)
    (hemb : Topology.IsEmbedding i)
    (himm : ∀ a, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) i a))
    {q : Z → X} (hcomp : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, F) ∞ (i ∘ q)) :
    ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ q := by
  intro z
  obtain ⟨U, hzU, r, hr, he⟩ := exists_localLeftInverse_of_embedding hi hemb himm (q z)
  let O : TopologicalSpace.Opens Z :=
    ⟨(i ∘ q) ⁻¹' U, U.isOpen.preimage hcomp.continuous⟩
  let a : O → U := fun y => ⟨i (q y.val), y.property⟩
  have ha : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, F) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff U a).mp
      (hcomp.comp contMDiff_subtype_val)
  have hqO : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun y : O => q y.val) := by
    have heq : (fun y : O => q y.val) = r ∘ a := by
      funext y
      exact (he (q y.val) y.property).symm
    rw [heq]
    exact hr.comp ha
  exact (contMDiffAt_subtype_iff (f := q) (x := (⟨z, hzU⟩ : O))).mp (hqO ⟨z, hzU⟩)

/-- Smooth scalar data on a compact carrier extend through its actual
injective immersion. Local inverse germs are constructed from the derivative,
so the desired ambient scalar is a conclusion rather than a hypothesis. -/
theorem exists_scalarExtension_of_compact_injective_immersion
    [T2Space X] [T2Space Y] [SecondCountableTopology Y]
    {A W : Set X} (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W)
    {j : X → Y} (hj : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ j W)
    (hinj : InjOn j A)
    (himm : ∀ x ∈ A, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) j x))
    {f : X → ℝ} (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f W) :
    ∃ g : Y → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g ∧
      ∀ x ∈ A, g (j x) = f x := by
  classical
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  let S := {x | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) j x)}
  have hSo : IsOpen S := isOpen_injective_mfderiv_on hW hj
  have hAS : A ⊆ S := fun x hx => ⟨hAW hx, himm x hx⟩
  have hloc : ∀ x ∈ A, ∃ u ∈ 𝓝 x, InjOn j u := by
    intro x hx
    obtain ⟨u, huo, hxu, _, hui, _⟩ :=
      exists_isOpen_injective_immersion_neighborhood hW hj (hAW hx) (himm x hx)
    exact ⟨u, huo.mem_nhds hxu, hui⟩
  obtain ⟨O, hOo, hAO, hOS, _, hemb⟩ :=
    exists_isOpen_embedding_neighborhood hA hSo hAS
      (hj.continuousOn.mono (fun _ hx => hx.1)) hinj hloc
  let o : TopologicalSpace.Opens X := ⟨O, hOo⟩
  have hOW : O ⊆ W := fun _ hx => (hOS (subset_closure hx)).1
  have hjo : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun x : o => j x.val) := by
    intro x
    exact (hj.contMDiffAt (hW.mem_nhds (hOW x.property))).comp x
      contMDiff_subtype_val.contMDiffAt
  have hfo : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : o => f x.val) := by
    intro x
    exact (hf.contMDiffAt (hW.mem_nhds (hOW x.property))).comp x
      contMDiff_subtype_val.contMDiffAt
  have hio (x : o) : Function.Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x : o => j x.val) x) := by
    change Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (j ∘ (Subtype.val : o → X)) x)
    rw [mfderiv_comp x
      ((hj.contMDiffAt (hW.mem_nhds (hOW x.property))).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))]
    have hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : o → X) x =
        ContinuousLinearMap.id ℝ E := by
      have he := mfderiv_comp (f := (Subtype.val : o → X))
        (g := chartAt E x.val) x
        ((mdifferentiable_chart (I := 𝓘(ℝ, E)) x.val).mdifferentiableAt
          (mem_chart_source _ _))
        ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
      have ha := mfderiv_extChartAt_self (I := 𝓘(ℝ, E)) (x := x.val)
      have hb := mfderiv_extChartAt_self (I := 𝓘(ℝ, E)) (x := x)
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x.val) x.val = _ at ha
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) x = _ at hb
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) x = _ at he
      erw [ha, hb] at he
      exact he.symm
    rw [hv]
    exact (hOS (subset_closure x.property)).2
  let B := j '' A
  have hB : IsClosed B := (hA.image_of_continuousOn (hj.continuousOn.mono hAW)).isClosed
  let b : Y → ℝ := fun y => if hy : ∃ x ∈ A, j x = y then f hy.choose else 0
  have hb (x : X) (hx : x ∈ A) : b (j x) = f x := by
    have he : ∃ y ∈ A, j y = j x := ⟨x, hx, rfl⟩
    have heq := hinj he.choose_spec.1 hx he.choose_spec.2
    simp only [b, dite_eq_left he, heq]
  have hgerms : ∀ y ∈ B, ∃ U ∈ 𝓝 y, ∃ g : Y → ℝ,
      ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g U ∧ EqOn g b (U ∩ B) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨U, hxU, r, hr, he⟩ := exists_localLeftInverse_of_embedding hjo hemb hio
      (⟨x, hAO hx⟩ : o)
    let g : Y → ℝ := fun y => if hy : y ∈ U then f (r ⟨y, hy⟩).val else 0
    have hs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y : U => g y.val) := by
      convert hfo.comp hr using 1
      funext y
      simp only [g, dite_eq_left y.property, Function.comp_apply]
    refine ⟨U, U.isOpen.mem_nhds hxU, g, ?_, ?_⟩
    · intro y hy
      exact ((contMDiffAt_subtype_iff (f := g) (x := (⟨y, hy⟩ : U))).mp
        (hs ⟨y, hy⟩)).contMDiffWithinAt
    · rintro y ⟨hyU, z, hz, rfl⟩
      have hleft := he (⟨z, hAO hz⟩ : o) hyU
      change (if hy : j z ∈ U then f (r ⟨j z, hy⟩).val else 0) = b (j z)
      simp only [show j z ∈ U from hyU, dite_true, hleft, hb z hz]
  obtain ⟨g, hg, heq⟩ := exists_contMDiff_scalarExtension_of_closed hB hgerms
  exact ⟨g, hg, fun x hx => (heq ⟨x, hx, rfl⟩).trans (hb x hx)⟩

end FsFltz.Geometry
