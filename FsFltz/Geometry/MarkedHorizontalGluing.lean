import FsFltz.Geometry.MarkedLevelHorizontalField
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Gluing native horizontal fields with simultaneous marked constraints

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
especially its affine gluing argument at lines 985–993.
The constructions retain actual tangent sections and all applicable affine
equations on a closed marked family. Compact transport is a later producer.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set Filter

namespace FsFltz.Geometry

section Components

variable {E F Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Q] [ChartedSpace E Q]

/-- The original marked augmented equation retains the unmarked parameter
and fiber equation and the actual truncation derivative simultaneously. -/
theorem parameter_marked_horizontal_components
    {τ ρ : Q → ℝ} {f : Q → F} {x : Q}
    (hτ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ x)
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x)
    (hρ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x)
    (v : TangentSpace 𝓘(ℝ, E) x)
    (hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × (F × ℝ))
      (fun q => (τ q, (f q, ρ q))) x v = (1, 0)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (fun q => (τ q, f q)) x v = (1, 0) ∧
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x v = 0 := by
  have h₁ := hτ.hasMFDerivAt
  have h₂ := hf.hasMFDerivAt
  have h₃ := hρ.hasMFDerivAt
  have hpair : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F)
      (fun q => (τ q, f q)) x
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ x).prod
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :=
    ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩
  have hmarked : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × (F × ℝ))
      (fun q => (τ q, (f q, ρ q))) x
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ x).prod
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).prod
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x))) :=
    ⟨h₁.1.prodMk (h₂.1.prodMk h₃.1), h₁.2.prodMk (h₂.2.prodMk h₃.2)⟩
  rw [hmarked.mfderiv] at hv
  rw [hpair.mfderiv]
  exact ⟨Prod.ext (congrArg (fun z : ℝ × (F × ℝ) => z.1) hv)
      (congrArg (fun z : ℝ × (F × ℝ) => z.2.1) hv),
    congrArg (fun z : ℝ × (F × ℝ) => z.2.2) hv⟩

end Components

section AffineGluing

variable {E F Q ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [SigmaCompactSpace Q]

/-- Local native fields satisfying all applicable marked affine equations
glue to one globally smooth field. The marked loci may be nested, overlap,
or be empty; every equation is retained on its own actual locus in `C`.
The hypotheses supply only local fields, and the global field is constructed
by the library's support-controlled smooth partition of unity. -/
theorem exists_smooth_marked_affine_lift
    (C : Set Q) (hC : IsClosed C) (S : ι → Set Q)
    (L : ι → (x : Q) → TangentSpace 𝓘(ℝ, E) x →L[ℝ] F)
    (b : ι → Q → F)
    (hloc : ∀ a ∈ C, ∃ (O : Set Q)
      (V : (x : Q) → TangentSpace 𝓘(ℝ, E) x), IsOpen O ∧ a ∈ O ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) O ∧
      ∀ j x, x ∈ O → x ∈ C → x ∈ S j → L j x (V x) = b j x) :
    ∃ V : (x : Q) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) ∧
      ∀ j x, x ∈ C → x ∈ S j → L j x (V x) = b j x := by
  let A (x : Q) : Set (TangentSpace 𝓘(ℝ, E) x) :=
    {v | ∀ j, x ∈ C → x ∈ S j → L j x v = b j x}
  have hconv : ∀ x, Convex ℝ (A x) := by
    intro x v hv w hw a b' _ha _hb hab j hx hs
    simp only [map_add, map_smul, hv j hx hs, hw j hx hs, ← add_smul, hab, one_smul]
  have hlocal : ∀ a : Q, ∃ O ∈ 𝓝 a,
      ∃ V : (x : Q) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
          (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) O ∧
        ∀ x ∈ O, V x ∈ A x := by
    intro a
    by_cases ha : a ∈ C
    · obtain ⟨O, V, hO, haO, hV, heq⟩ := hloc a ha
      exact ⟨O, hO.mem_nhds haO, V, hV, fun x hx j hxc hxs => heq j x hx hxc hxs⟩
    · refine ⟨Cᶜ, hC.isOpen_compl.mem_nhds ha, fun _ => 0,
        (Bundle.contMDiff_zeroSection ℝ
          (TangentSpace 𝓘(ℝ, E))).contMDiffOn, ?_⟩
      intro x hx j hxc _hxs
      exact False.elim (hx hxc)
  obtain ⟨V, hV⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    𝓘(ℝ, E) (TangentSpace 𝓘(ℝ, E)) A hconv hlocal
  exact ⟨fun x => V x, V.contMDiff, fun j x hx hs => hV x j hx hs⟩

end AffineGluing

section NeighborhoodGluing

variable {E F Q ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [SigmaCompactSpace Q] [NormalSpace Q]

/-- If the local equations hold wherever their marked loci meet the local
open sources, the glued field satisfies them on an actual open neighborhood
of the compact family. In particular the parameter and fiber equations may
be imposed on `S j = univ`, keeping them valid along nearby trajectories. -/
theorem exists_smooth_marked_affine_lift_near_compact
    (C : Set Q) (hC : IsCompact C) (S : ι → Set Q)
    (L : ι → (x : Q) → TangentSpace 𝓘(ℝ, E) x →L[ℝ] F)
    (b : ι → Q → F)
    (hloc : ∀ a ∈ C, ∃ (O : Set Q)
      (V : (x : Q) → TangentSpace 𝓘(ℝ, E) x), IsOpen O ∧ a ∈ O ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) O ∧
      ∀ j x, x ∈ O → x ∈ S j → L j x (V x) = b j x) :
    ∃ (O : Set Q) (V : (x : Q) → TangentSpace 𝓘(ℝ, E) x),
      IsOpen O ∧ C ⊆ O ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) ∧
      ∀ j x, x ∈ O → x ∈ S j → L j x (V x) = b j x := by
  classical
  choose W V hW haW hV heq using (fun a : C => hloc a a.property)
  let U : Set Q := ⋃ a : C, W a
  have hU : IsOpen U := isOpen_iUnion hW
  have hCU : C ⊆ U := fun a ha => mem_iUnion_of_mem ⟨a, ha⟩ (haW ⟨a, ha⟩)
  obtain ⟨O, hO, hCO, hOU⟩ := normal_exists_closure_subset hC.isClosed hU hCU
  obtain ⟨Z, hZ, hZe⟩ := exists_smooth_marked_affine_lift (closure O)
    isClosed_closure S L b (by
      intro a ha
      obtain ⟨i, hai⟩ := mem_iUnion.mp (hOU ha)
      exact ⟨W i, V i, hW i, hai, hV i, fun j x hx _hxc hs => heq i j x hx hs⟩)
  exact ⟨O, Z, hO, hCO, hZ, fun j x hx hs => hZe j x (subset_closure hx) hs⟩

/-- Local horizontal lifts and local lifts of a closed marked boundary
construct one field satisfying the horizontal equations on a neighborhood
of the whole compact family and the additional equations on a neighborhood
of its marked boundary. The extra equations hold on an open collar, not
merely at boundary points. No global lift or transport is assumed. -/
theorem exists_smooth_boundary_horizontal_lift_near_compact
    (C : Set Q) (hC : IsCompact C) (T : Set Q) (hT : IsClosed T)
    (L H : (x : Q) → TangentSpace 𝓘(ℝ, E) x →L[ℝ] F) (b c : Q → F)
    (hloc : ∀ a ∈ C, ∃ (O : Set Q)
      (V : (x : Q) → TangentSpace 𝓘(ℝ, E) x), IsOpen O ∧ a ∈ O ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) O ∧
      ∀ x ∈ O, L x (V x) = b x)
    (hmarked : ∀ a ∈ C ∩ T, ∃ (O : Set Q)
      (V : (x : Q) → TangentSpace 𝓘(ℝ, E) x), IsOpen O ∧ a ∈ O ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) O ∧
      ∀ x ∈ O, L x (V x) = b x ∧ H x (V x) = c x) :
    ∃ (O B : Set Q) (V : (x : Q) → TangentSpace 𝓘(ℝ, E) x),
      IsOpen O ∧ C ⊆ O ∧ IsOpen B ∧ C ∩ T ⊆ B ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) ∧
      (∀ x ∈ O, L x (V x) = b x) ∧
      ∀ x ∈ O ∩ B, H x (V x) = c x := by
  classical
  choose W V hW haW hV heq using (fun a : ↥(C ∩ T) => hmarked a a.property)
  let U : Set Q := ⋃ a : ↥(C ∩ T), W a
  have hU : IsOpen U := isOpen_iUnion hW
  have hCU : C ∩ T ⊆ U := fun a ha => mem_iUnion_of_mem ⟨a, ha⟩ (haW ⟨a, ha⟩)
  obtain ⟨B, hB, hCB, hBU⟩ := normal_exists_closure_subset
    (hC.isClosed.inter hT) hU hCU
  let S : Bool → Set Q := fun j => if j then closure B else univ
  let A : Bool → (x : Q) → TangentSpace 𝓘(ℝ, E) x →L[ℝ] F :=
    fun j => if j then H else L
  let d : Bool → Q → F := fun j => if j then c else b
  have hall : ∀ a ∈ C, ∃ (P : Set Q)
      (Z : (x : Q) → TangentSpace 𝓘(ℝ, E) x), IsOpen P ∧ a ∈ P ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, Z x⟩ : TangentBundle 𝓘(ℝ, E) Q)) P ∧
      ∀ j x, x ∈ P → x ∈ S j → A j x (Z x) = d j x := by
    intro a ha
    by_cases hab : a ∈ closure B
    · obtain ⟨i, hai⟩ := mem_iUnion.mp (hBU hab)
      refine ⟨W i, V i, hW i, hai, hV i, ?_⟩
      intro j x hx _hs
      cases j
      · exact (heq i x hx).1
      · exact (heq i x hx).2
    · obtain ⟨P, Z, hP, haP, hZ, hL⟩ := hloc a ha
      refine ⟨P ∩ (closure B)ᶜ, Z, hP.inter isClosed_closure.isOpen_compl,
        ⟨haP, hab⟩, hZ.mono inter_subset_left, ?_⟩
      intro j x hx hs
      cases j
      · exact hL x hx.1
      · exact False.elim (hx.2 hs)
  obtain ⟨O, Z, hO, hCO, hZ, hZe⟩ :=
    exists_smooth_marked_affine_lift_near_compact C hC S A d hall
  exact ⟨O, B, Z, hO, hCO, hB, hCB, hZ,
    fun x hx => hZe false x hx (mem_univ _),
    fun x hx => hZe true x hx.1 (subset_closure hx.2)⟩

end NeighborhoodGluing

end FsFltz.Geometry
