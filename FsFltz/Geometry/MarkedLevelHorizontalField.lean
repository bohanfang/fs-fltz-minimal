import FsFltz.Geometry.MarkedLevelFamily
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Actual local horizontal fields for marked parameter levels

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 985–1003.
The inverse differential of the actual joint normal form transports the
constant parameter-coordinate field. It is a smooth native tangent section
and satisfies the original affine lift equations on its open source.
Partition gluing and compact global transport are separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

section CoordinateField

variable {E W Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- Pulling a constant coordinate field through the inverse of an actual
partial diffeomorphism gives a smooth native tangent-bundle section on its
open source. -/
theorem contMDiffOn_inverse_coordinateField
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, W) Q W ∞) (v : W) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) e.invFun (e x) v⟩ :
        TangentBundle 𝓘(ℝ, E) Q)) e.source := by
  have hsec : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, W)).tangent ∞
      (fun x => (⟨e x, v⟩ : TangentBundle 𝓘(ℝ, W) W)) e.source := by
    let : ChartedSpace (W × W) (ModelProd W W) :=
      inferInstanceAs (ChartedSpace (W × W) (W × W))
    have hh : ContMDiff 𝓘(ℝ, W × W) (𝓘(ℝ, W)).tangent ∞
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, W)).symm := by
      simpa only [ModelWithCorners.tangent, ← modelWithCornersSelf_prod] using
        (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, W)) (n := ∞))
    exact hh.comp_contMDiffOn
      (e.contMDiffOn_toFun.prodMk_space (contMDiffOn_const (c := v)))
  have ht := e.contMDiffOn_invFun.contMDiffOn_tangentMapWithin
    (m := ∞) (by simp) e.open_target.uniqueMDiffOn
  have hcomp := ht.comp hsec (fun x hx => e.toOpenPartialHomeomorph.map_source hx)
  apply hcomp.congr
  intro x hx
  dsimp only [Function.comp_def, tangentMapWithin]
  have hleft : e.invFun (e x) = x := e.toOpenPartialHomeomorph.left_inv hx
  have hD : mfderivWithin 𝓘(ℝ, W) 𝓘(ℝ, E) e.invFun e.target (e x) =
      mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) e.invFun (e x) :=
    mfderivWithin_of_mem_nhds
      (e.open_target.mem_nhds (e.toOpenPartialHomeomorph.map_source hx))
  simp only [hD]
  exact Bundle.TotalSpace.ext hleft.symm (HEq.refl _)

end CoordinateField

section HorizontalField

variable {E F K Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- An actual joint normal form produces a smooth local horizontal field.
Its derivative under the original parameter-and-equations map is exactly
the parameter direction, so all actual level equations have zero derivative.
The lift is constructed, not supplied as an additional hypothesis. -/
theorem exists_local_marked_horizontalField
    (g : Q → ℝ × F) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) ∞ g)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, (ℝ × F) × K) Q ((ℝ × F) × K) ∞)
    (he : ∀ x ∈ e.source, (e x).1 = g x) :
    ∃ V : (x : Q) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) e.source ∧
      ∀ x ∈ e.source, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) g x (V x) = (1, 0) := by
  let v : (ℝ × F) × K := ((1, 0), 0)
  let V : (x : Q) → TangentSpace 𝓘(ℝ, E) x :=
    fun x => mfderiv 𝓘(ℝ, (ℝ × F) × K) 𝓘(ℝ, E) e.invFun (e x) v
  refine ⟨V, contMDiffOn_inverse_coordinateField e v, ?_⟩
  intro x hx
  have hxt : e x ∈ e.target := e.toOpenPartialHomeomorph.map_source hx
  have hagree : g ∘ e.invFun =ᶠ[𝓝 (e x)] (Prod.fst : ((ℝ × F) × K) → ℝ × F) := by
    filter_upwards [e.open_target.mem_nhds hxt] with y hy
    have hys : e.invFun y ∈ e.source := e.toOpenPartialHomeomorph.map_target hy
    have hright : e (e.invFun y) = y := e.toOpenPartialHomeomorph.right_inv hy
    exact (he (e.invFun y) hys).symm.trans (congrArg Prod.fst hright)
  have hder : mfderiv 𝓘(ℝ, (ℝ × F) × K) 𝓘(ℝ, ℝ × F) (g ∘ e.invFun) (e x) =
      ContinuousLinearMap.fst ℝ (ℝ × F) K := by
    rw [Filter.EventuallyEq.mfderiv_eq hagree]
    exact (ContinuousLinearMap.fst ℝ (ℝ × F) K).hasFDerivAt.hasMFDerivAt.mfderiv
  have hleft : e.invFun (e x) = x := e.toOpenPartialHomeomorph.left_inv hx
  have hchain := mfderiv_comp (I := 𝓘(ℝ, (ℝ × F) × K))
    (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, ℝ × F)) (e x)
    (hg.mdifferentiableAt (by simp))
    ((e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hxt)).mdifferentiableAt
      (by simp))
  rw [hchain, hleft] at hder
  exact congrArg (fun L => L v) hder

end HorizontalField

section ParameterField

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Joint smooth actual equations and spatial regularity construct an
actual smooth horizontal lift on a nonempty open neighborhood of the
specified parameter-space point. Neither the normal form nor the lift
is part of the hypotheses. Taking `F = ℂ × ℝ` retains both real fiber
equations and the potential-boundary equation in the same lift. -/
theorem exists_parameter_level_horizontalField {f : ℝ × M → F} {a : ℝ × M}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ f)
    (hd : Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x => f (a.1, x)) a.2)) :
    letI : ChartedSpace (ℝ × E) (ℝ × M) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ E) (ℝ × M))
    letI : IsManifold 𝓘(ℝ, ℝ × E) ∞ (ℝ × M) := by
      rw [modelWithCornersSelf_prod]
      exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (ℝ × M))
    ∃ (O : Set (ℝ × M)) (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ, ℝ × E) p),
      IsOpen O ∧ a ∈ O ∧
      ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ × E)).tangent ∞
        (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × M))) O ∧
      ∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F)
        (fun q : ℝ × M => (q.1, f q)) p (V p) = (1, 0) := by
  let : ChartedSpace (ℝ × E) (ℝ × M) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ E) (ℝ × M))
  let : IsManifold 𝓘(ℝ, ℝ × E) ∞ (ℝ × M) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (ℝ × M))
  have hg : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞
      (fun q : ℝ × M => (q.1, f q)) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst.prodMk_space hf
  obtain ⟨e, ha, he⟩ := exists_parameter_level_kernel_normalForm hf hd
  obtain ⟨V, hV, hder⟩ := exists_local_marked_horizontalField
    (fun q : ℝ × M => (q.1, f q)) hg e he
  exact ⟨e.source, V, e.open_source, ha, hV, hder⟩

end ParameterField

end FsFltz.Geometry
