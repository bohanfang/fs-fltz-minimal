import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Relative target-chart patching of smooth partial maps

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:pair`,
132–146, `def:chain`, 163–169, and `sec:lean`, 788–814.
The correction below uses a target chart only over the new local patch;
the previously constructed map outside that patch is unrestricted.
All maps have their actual open domains, so an empty target requires no
chosen default point.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter IsManifold

namespace FsFltz.Geometry.SmoothMapExtension

variable {E F X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace N] [ChartedSpace F N]

set_option backward.isDefEq.respectTransparency false

/-- Smooth partial maps which agree on their actual overlap glue on the
union of their open domains. This lemma supplies the final gluing only;
the chart correction below constructs the required overlap agreement. -/
theorem exists_smooth_open_gluing
    (U V : TopologicalSpace.Opens X) (f : U → N) (g : V → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (heq : ∀ x (hU : x ∈ U) (hV : x ∈ V), f ⟨x, hU⟩ = g ⟨x, hV⟩) :
    ∃ h : ↥(U ⊔ V) → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h ∧
      (∀ x (hx : x ∈ U), h ⟨x, Or.inl hx⟩ = f ⟨x, hx⟩) ∧
      (∀ x (hx : x ∈ V), h ⟨x, Or.inr hx⟩ = g ⟨x, hx⟩) := by
  classical
  let h : ↥(U ⊔ V) → N := fun p =>
    if hp : p.val ∈ U then f ⟨p.val, hp⟩
    else g ⟨p.val, p.property.resolve_left hp⟩
  have hleft : ∀ x (hx : x ∈ U), h ⟨x, Or.inl hx⟩ = f ⟨x, hx⟩ := by
    intro x hx
    simp only [h, dite_eq_left hx]
  have hright : ∀ x (hx : x ∈ V), h ⟨x, Or.inr hx⟩ = g ⟨x, hx⟩ := by
    intro x hx
    by_cases hxU : x ∈ U
    · simpa only [h, dite_eq_left hxU] using heq x hxU hx
    · simp only [h, dite_eq_right hxU]
  refine ⟨h, ?_, hleft, hright⟩
  intro p
  rcases p.property with hp | hp
  · let Q : TopologicalSpace.Opens ↥(U ⊔ V) :=
      ⟨Subtype.val ⁻¹' U, U.isOpen.preimage continuous_subtype_val⟩
    let a : Q → U := fun q => ⟨q.val.val, q.property⟩
    have ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ a :=
      (ContMDiff.subtypeVal_comp_iff U a).mp
        ((contMDiff_subtype_val (U := U ⊔ V)).comp
          (contMDiff_subtype_val (U := Q)))
    have hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun q : Q => h q.val) := by
      have he : (fun q : Q => h q.val) = f ∘ a := by
        funext q
        exact hleft q.val.val q.property
      rw [he]
      exact hf.comp ha
    exact (contMDiffAt_subtype_iff (f := h) (x := (⟨p, hp⟩ : Q))).mp
      (hr ⟨p, hp⟩)
  · let Q : TopologicalSpace.Opens ↥(U ⊔ V) :=
      ⟨Subtype.val ⁻¹' V, V.isOpen.preimage continuous_subtype_val⟩
    let a : Q → V := fun q => ⟨q.val.val, q.property⟩
    have ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ a :=
      (ContMDiff.subtypeVal_comp_iff V a).mp
        ((contMDiff_subtype_val (U := U ⊔ V)).comp
          (contMDiff_subtype_val (U := Q)))
    have hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun q : Q => h q.val) := by
      have he : (fun q : Q => h q.val) = g ∘ a := by
        funext q
        exact hright q.val.val q.property
      rw [he]
      exact hg.comp ha
    exact (contMDiffAt_subtype_iff (f := h) (x := (⟨p, hp⟩ : Q))).mp
      (hr ⟨p, hp⟩)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ X]
  [T2Space X] [SecondCountableTopology X]

/-- A compact cutoff retaining the convex-combination bounds. Its plateau
is an open neighborhood contained in the prescribed patch. -/
theorem exists_bounded_smooth_compact_cutoff
    {K : Set X} (hK : IsCompact K) (U : TopologicalSpace.Opens X)
    (hKU : K ⊆ U) :
    ∃ (χ : X → ℝ) (P : TopologicalSpace.Opens X),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ K ⊆ P ∧ P ≤ U ∧
      (∀ x ∈ P, χ x = 1) ∧ IsCompact (tsupport χ) ∧ tsupport χ ⊆ U := by
  let := ChartedSpace.locallyCompactSpace E X
  obtain ⟨B, hBo, hKB, hBc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨S, hSo, hKS, hSc⟩ := hK.exists_isOpen_closure_subset
    ((U.isOpen.inter hBo).mem_nhdsSet.mpr (subset_inter hKU hKB))
  obtain ⟨P, hPo, hKP, hPc⟩ :=
    hK.exists_isOpen_closure_subset (hSo.mem_nhdsSet.mpr hKS)
  obtain ⟨χ, hχ, hχrange, hχS, hχP⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, E)
      (n := ⊤) hSo isClosed_closure hPc
  have hcompact : IsCompact (closure S) :=
    hBc.of_isClosed_subset isClosed_closure
      (hSc.trans (inter_subset_right.trans subset_closure))
  have hSU : closure S ⊆ U := hSc.trans inter_subset_left
  refine ⟨χ, ⟨P, hPo⟩, hχ, ?_, hKP,
    subset_closure.trans (hPc.trans (subset_closure.trans hSU)), ?_, ?_, ?_⟩
  · intro x
    exact hχrange (mem_range_self x)
  · intro x hx
    exact (hχP x).mp (subset_closure hx)
  · simpa only [tsupport, hχS] using hcompact
  · simpa only [tsupport, hχS] using hSU

/-- Add one compact germ patch to an existing smooth partial map. The old
map is required to enter the chosen convex target chart only on the local
overlap. The germs need agree only on the prescribed carrier, not away from
it. The output supplies one smooth map on the enlarged open domain. -/
theorem exists_chart_patch_extension
    (V U : TopologicalSpace.Opens X) (f : V → N) (g : U → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (e : OpenPartialHomeomorph N F)
    (he : e ∈ maximalAtlas 𝓘(ℝ, F) ∞ N)
    (C : Set F) (hC : Convex ℝ C) (hCe : C ⊆ e.target)
    (hge : ∀ x : U, g x ∈ e.source ∧ e (g x) ∈ C)
    (hfe : ∀ x : V, x.val ∈ U → f x ∈ e.source ∧ e (f x) ∈ C)
    (A : Set X) (f₀ : A → N)
    (hfA : ∀ x : V, ∀ hx : x.val ∈ A, f x = f₀ ⟨x.val, hx⟩)
    (hgA : ∀ x : U, ∀ hx : x.val ∈ A, g x = f₀ ⟨x.val, hx⟩)
    (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ P : TopologicalSpace.Opens X, K ⊆ P ∧ P ≤ U ∧
      ∃ h : ↥(V ⊔ P) → N,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h ∧
        (∀ x : ↥(V ⊔ P), ∀ hx : x.val ∈ A, h x = f₀ ⟨x.val, hx⟩) ∧
        (∀ x (hxP : x ∈ P) (hxU : x ∈ U),
          h ⟨x, Or.inr hxP⟩ = g ⟨x, hxU⟩) ∧
        ∃ S : Set X, IsCompact S ∧ S ⊆ U ∧
          ∀ x (hxV : x ∈ V), x ∉ S →
            h ⟨x, Or.inl hxV⟩ = f ⟨x, hxV⟩ := by
  classical
  obtain ⟨χ, P, hχ, hχrange, hKP, hPU, hχP, hχcompact, hχU⟩ :=
    exists_bounded_smooth_compact_cutoff (E := E) hK U hKU
  let Q : TopologicalSpace.Opens V :=
    ⟨Subtype.val ⁻¹' U, U.isOpen.preimage continuous_subtype_val⟩
  let gQ : Q → N := fun q => g ⟨q.val.val, q.property⟩
  let fQ : Q → N := fun q => f q.val
  let χQ : Q → ℝ := fun q => χ q.val.val
  have hvv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun q : Q => q.val.val) :=
    (contMDiff_subtype_val (U := V)).comp (contMDiff_subtype_val (U := Q))
  have hfQ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ fQ :=
    hf.comp contMDiff_subtype_val
  have hgQ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ gQ := by
    let a : Q → U := fun q => ⟨q.val.val, q.property⟩
    have ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ a :=
      (ContMDiff.subtypeVal_comp_iff U a).mp hvv
    exact hg.comp ha
  have hχQ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χQ := hχ.comp hvv
  have hef : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun q : Q => e (fQ q)) := by
    intro q
    exact (contMDiffAt_of_mem_maximalAtlas he (hfe q.val q.property).1).comp q (hfQ q)
  have heg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun q : Q => e (gQ q)) := by
    intro q
    exact (contMDiffAt_of_mem_maximalAtlas he (hge ⟨q.val.val, q.property⟩).1).comp
      q (hgQ q)
  let z : Q → F := fun q => (1 - χQ q) • e (fQ q) + χQ q • e (gQ q)
  have hz : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ z :=
    ((contMDiff_const.sub hχQ).smul hef).add (hχQ.smul heg)
  have hze : ∀ q, z q ∈ e.target := by
    intro q
    apply hCe
    exact hC (hfe q.val q.property).2 (hge ⟨q.val.val, q.property⟩).2
      (sub_nonneg.mpr (hχrange q.val.val).2) (hχrange q.val.val).1 (by ring)
  have hzmap : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun q : Q => e.symm (z q)) := by
    intro q
    exact (contMDiffAt_symm_of_mem_maximalAtlas he (hze q)).comp q (hz q)
  let r : V → N := fun x =>
    if hx : x.val ∈ U then e.symm (z ⟨x, hx⟩) else f x
  have hrQ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun q : Q => r q.val) := by
    have heq : (fun q : Q => r q.val) = (fun q => e.symm (z q)) := by
      funext q
      have hq : q.val.val ∈ U := q.property
      simp only [r, dite_eq_left hq]
    rw [heq]
    exact hzmap
  have hrzero : ∀ x : V, χ x.val = 0 → r x = f x := by
    intro x hx
    by_cases hxU : x.val ∈ U
    · simp only [r, dite_eq_left hxU, z, χQ, fQ, gQ, hx,
        sub_zero, one_smul, zero_smul, add_zero]
      exact e.left_inv (hfe x hxU).1
    · simp only [r, dite_eq_right hxU]
  have hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ r := by
    intro x
    by_cases hxU : x.val ∈ U
    · exact (contMDiffAt_subtype_iff (f := r) (x := (⟨x, hxU⟩ : Q))).mp
        (hrQ ⟨x, hxU⟩)
    · have hxS : x.val ∉ tsupport χ := fun hx => hxU (hχU hx)
      have hnhds : ∀ᶠ y : V in 𝓝 x, y.val ∉ tsupport χ :=
        (isClosed_tsupport χ).isOpen_compl.preimage continuous_subtype_val |>.mem_nhds hxS
      exact (hf x).congr_of_eventuallyEq (hnhds.mono (fun y hy =>
        hrzero y (image_eq_zero_of_notMem_tsupport hy)))
  have hrA : ∀ x : V, ∀ hx : x.val ∈ A, r x = f₀ ⟨x.val, hx⟩ := by
    intro x hxA
    by_cases hxU : x.val ∈ U
    · have heq : g ⟨x.val, hxU⟩ = f x :=
        (hgA ⟨x.val, hxU⟩ hxA).trans (hfA x hxA).symm
      have hsum : (1 - χ x.val) + χ x.val = 1 := by ring
      simp only [r, dite_eq_left hxU, z, χQ, fQ, gQ, heq,
        ← add_smul, hsum, one_smul]
      exact (e.left_inv (hfe x hxU).1).trans (hfA x hxA)
    · simpa only [r, dite_eq_right hxU] using hfA x hxA
  have hrP : ∀ x (hxV : x ∈ V) (hxP : x ∈ P),
      r ⟨x, hxV⟩ = g ⟨x, hPU hxP⟩ := by
    intro x hxV hxP
    simp only [r, dite_eq_left (hPU hxP), z, χQ, fQ, gQ,
      hχP x hxP, sub_self, zero_smul, one_smul, zero_add]
    exact e.left_inv (hge ⟨x, hPU hxP⟩).1
  let gP : P → N := g ∘ TopologicalSpace.Opens.inclusion hPU
  have hgP : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ gP :=
    hg.comp (contMDiff_inclusion hPU)
  obtain ⟨h, hh, hhV, hhP⟩ := exists_smooth_open_gluing V P r gP hr hgP hrP
  refine ⟨P, hKP, hPU, h, hh, ?_, ?_, tsupport χ, hχcompact, hχU, ?_⟩
  · intro x hxA
    rcases x.property with hxV | hxP
    · exact (hhV x.val hxV).trans (hrA ⟨x.val, hxV⟩ hxA)
    · exact (hhP x.val hxP).trans (hgA ⟨x.val, hPU hxP⟩ hxA)
  · intro x hxP hxU
    exact hhP x hxP
  · intro x hxV hxS
    exact (hhV x hxV).trans (hrzero ⟨x, hxV⟩ (image_eq_zero_of_notMem_tsupport hxS))

end FsFltz.Geometry.SmoothMapExtension
