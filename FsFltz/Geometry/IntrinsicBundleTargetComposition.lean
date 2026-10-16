import FsFltz.Geometry.IntrinsicBundleNativeData

/-!
# Varying target composition of actual bundle germs

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. A target-valued local map germ composes with a varying native
target-map germ on the same original parameter set. This is the operation
needed to transport ribbon values through a varying ambient boundary chart.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {d : ℕ} {H F : Type*} [TopologicalSpace H] [TopologicalSpace F]
  {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H F]

/-- A target-valued germ, paired with its unchanged real parameter, is a
smooth map on its actual open model domain. The auxiliary extension outside
that domain is used only to describe an open preimage. -/
private theorem target_germ_pair {r : ℕ} (N : SmoothManifold r)
    (U : TopologicalSpace.Opens (ℝ × Model d)) (β : U → N.Point)
    (hβ : ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, Model r) ∞ β)
    (y₀ : N.Point) :
    ∃ q : ℝ × Model d → ℝ × N.Point,
      ContMDiffOn 𝓘(ℝ, ℝ × Model d) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) ∞ q U ∧
      ∀ z (hz : z ∈ U), q z = (z.1, β ⟨z, hz⟩) := by
  classical
  let q : ℝ × Model d → ℝ × N.Point :=
    fun z => (z.1, if h : z ∈ U then β ⟨z, h⟩ else y₀)
  have he (z : ℝ × Model d) (hz : z ∈ U) : q z = (z.1, β ⟨z, hz⟩) := by
    simp only [q, dite_eq_left hz]
  have hr : ContMDiff 𝓘(ℝ, ℝ × Model d)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) ∞ (fun z : U => q z.val) := by
    have hp := (contDiff_fst.contMDiff.comp contMDiff_subtype_val).prodMk hβ
    exact hp.congr (fun z => he z.val z.property)
  refine ⟨q, ?_, he⟩
  intro z hz
  exact ((contMDiffAt_subtype_iff (f := q) (x := (⟨z, hz⟩ : U))).mp
    hr.contMDiffAt).contMDiffWithinAt

/-- Genuine target-valued joint germs compose with a varying target map.
Both map families are defined only on the original interval parameter set. -/
theorem HasSmoothTargetFamilyOn.postcomp {r m : ℕ}
    (N : SmoothManifold r) (P : SmoothManifold m) {S : Set Parameter}
    {v : Parameter → F → N.Point} (hv : HasSmoothTargetFamilyOn I N S v)
    {g : Parameter → N.Point → P.Point} (hg : HasSmoothManifoldTargetFamilyOn N P S g) :
    HasSmoothTargetFamilyOn I P S (fun t x => g t (v t x)) := by
  intro a ha t ht x hx
  obtain ⟨U, hpU, β, hβ, heqβ⟩ := hv a ha t ht x hx
  obtain ⟨V, hpV, γ, hγ, heqγ⟩ := hg t ht (v t x)
  obtain ⟨q, hq, heq⟩ := target_germ_pair N U β hβ (v t x)
  let O : TopologicalSpace.Opens (ℝ × Model d) :=
    ⟨(U : Set (ℝ × Model d)) ∩ q ⁻¹' V,
      hq.continuousOn.isOpen_inter_preimage U.isOpen V.isOpen⟩
  let Q : O → V := fun z => ⟨q z.val, z.property.2⟩
  have hQ : ContMDiff 𝓘(ℝ, ℝ × Model d)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) ∞ Q := by
    apply (ContMDiff.subtypeVal_comp_iff V Q).mp
    intro z
    exact (hq.contMDiffAt (U.isOpen.mem_nhds z.property.1)).comp
      z contMDiff_subtype_val.contMDiffAt
  have hqcenter : q (t.val, a.extend I x) = (t.val, v t x) := by
    rw [heq _ hpU, heqβ t ht x hx hpU]
  refine ⟨O, ⟨hpU, by change q (t.val, a.extend I x) ∈ V; rw [hqcenter]; exact hpV⟩,
    γ ∘ Q, hγ.comp hQ, ?_⟩
  intro s hs y hy hsy
  have hqy : q (s.val, a.extend I y) = (s.val, v s y) := by
    rw [heq _ hsy.1, heqβ s hs y hy hsy.1]
  have hmid : (s.val, v s y) ∈ V := by
    have h := hsy.2
    change q (s.val, a.extend I y) ∈ V at h
    rwa [hqy] at h
  have harg : Q ⟨(s.val, a.extend I y), hsy⟩ = ⟨(s.val, v s y), hmid⟩ :=
    Subtype.ext hqy
  exact (congrArg γ harg).trans (heqγ s hs (v s y) hmid)

/-- Joint value germs on a boundaryless native source, restricted to its
original parameter set. -/
def HasSmoothManifoldValueFamilyOn {r : ℕ} (N : SmoothManifold r) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Set Parameter)
    (v : Parameter → N.Point → V) : Prop :=
  ∀ t ∈ S, ∀ x : N.Point,
    ∃ (U : Set (ℝ × N.Point)) (β : ℝ × N.Point → V), IsOpen U ∧ (t.val, x) ∈ U ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) 𝓘(ℝ, V) ∞ β U ∧
      ∀ s ∈ S, ∀ y : N.Point, (s.val, y) ∈ U → β (s.val, y) = v s y

theorem HasSmoothValueFamilyOn.native_value {r : ℕ} (N : SmoothManifold r)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {S : Set Parameter}
    {v : Parameter → N.Point → V} (hv : HasSmoothValueFamilyOn 𝓘(ℝ, Model r) S v) :
    HasSmoothManifoldValueFamilyOn N S v := by
  intro t ht x
  let a := chartAt (Model r) x
  have hx : x ∈ a.source := mem_chart_source _ _
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ := hv a (chart_mem_atlas _ _) t ht x hx
  let p : ℝ × N.Point → ℝ × Model r := fun z => (z.1, a.extend 𝓘(ℝ, Model r) z.2)
  have ha : ContMDiffOn 𝓘(ℝ, Model r) 𝓘(ℝ, Model r) ∞
      (a.extend 𝓘(ℝ, Model r)) a.source :=
    a.contMDiffOn_extend (IsManifold.subset_maximalAtlas (chart_mem_atlas _ x))
  have hp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r))
      𝓘(ℝ, ℝ × Model r) ∞ p (univ ×ˢ a.source) :=
    contMDiff_fst.contMDiffOn.prodMk_space
      (ha.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
  exact ⟨(univ ×ˢ a.source) ∩ p ⁻¹' U, β ∘ p,
    hp.continuousOn.isOpen_inter_preimage (isOpen_univ.prod a.open_source) hU,
    ⟨⟨mem_univ _, hx⟩, hpU⟩,
    hβ.contMDiffOn.comp (hp.mono inter_subset_left) (fun _ hz => hz.2),
    fun s hs y hy => heq s hs y hy.1.2 hy.2⟩

/-- Pull a varying native target value through an actual target-valued
source map germ. In particular this transports positive boundary witnesses. -/
theorem HasSmoothTargetFamilyOn.postcomp_value {r : ℕ} (N : SmoothManifold r)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {S : Set Parameter}
    {f : Parameter → F → N.Point} (hf : HasSmoothTargetFamilyOn I N S f)
    {v : Parameter → N.Point → V} (hv : HasSmoothManifoldValueFamilyOn N S v) :
    HasSmoothValueFamilyOn I S (fun t x => v t (f t x)) := by
  intro a ha t ht x hx
  obtain ⟨U, hpU, β, hβ, heqβ⟩ := hf a ha t ht x hx
  obtain ⟨W, γ, hW, hpW, hγ, heqγ⟩ := hv t ht (f t x)
  obtain ⟨q, hq, heq⟩ := target_germ_pair N U β hβ (f t x)
  let O : Set (ℝ × Model d) := (U : Set (ℝ × Model d)) ∩ q ⁻¹' W
  have hO : IsOpen O := hq.continuousOn.isOpen_inter_preimage U.isOpen hW
  have hqcenter : q (t.val, a.extend I x) = (t.val, f t x) := by
    rw [heq _ hpU, heqβ t ht x hx hpU]
  have hsm : ContDiffOn ℝ ∞ (γ ∘ q) O :=
    (hγ.comp (hq.mono inter_subset_left) (fun _ hz => hz.2)).contDiffOn
  refine ⟨O, γ ∘ q, hO,
    ⟨hpU, by change q (t.val, a.extend I x) ∈ W; rw [hqcenter]; exact hpW⟩,
    hsm, ?_⟩
  intro s hs y hy hsy
  have hqy : q (s.val, a.extend I y) = (s.val, f s y) := by
    rw [heq _ hsy.1, heqβ s hs y hy hsy.1]
  have hmid : (s.val, f s y) ∈ W := by
    have h := hsy.2
    change q (s.val, a.extend I y) ∈ W at h
    rwa [hqy] at h
  change γ (q (s.val, a.extend I y)) = _
  rw [hqy]
  exact heqγ s hs (f s y) hmid

end FsFltz.Geometry.IntrinsicSmoothBundle
