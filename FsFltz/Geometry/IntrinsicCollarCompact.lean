import FsFltz.Geometry.IntrinsicCollarGlobalUniqueness
import FsFltz.Geometry.IntrinsicCollarCoefficients
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Compact assembly of native inward collars

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. The local maps below are actual solutions of
one native field. Compactness constructs their common positive width;
native ODE uniqueness supplies their overlap identities. Boundaryless
extension and the completed Liouville primitive are later consumers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

/-- An open cover of a compact space with positive local widths has a
finite subcover and one strictly positive lower bound for its widths.
The empty space has the explicit width one. -/
theorem exists_pos_finite_subcover {B ι : Type*} [TopologicalSpace B]
    [CompactSpace B] (U : ι → Set B) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ (s : Finset ι) (δ : ℝ), 0 < δ ∧ (∀ i ∈ s, δ ≤ d i) ∧
      ∀ x, ∃ i ∈ s, x ∈ U i := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, hi⟩)
  have hcov : ∀ x, ∃ i ∈ s, x ∈ U i := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (mem_univ x))
    obtain ⟨his, hx⟩ := mem_iUnion.mp hi
    exact ⟨i, his, hx⟩
  by_cases hne : s.Nonempty
  · obtain ⟨i, hi, hmin⟩ := s.exists_min_image d hne
    exact ⟨s, d i, hd i, hmin, hcov⟩
  · refine ⟨s, 1, by norm_num, ?_, hcov⟩
    intro i hi
    exact (hne ⟨i, hi⟩).elim

/-- A local homeomorphism on a one-sided strip whose compact seam is
injective is an open embedding on a smaller common strip. No injectivity
away from the seam is assumed. -/
theorem exists_pos_openEmbedding_of_localHomeomorph
    {B N : Type*} [TopologicalSpace B] [CompactSpace B]
    [TopologicalSpace N] [T2Space N] {F : ℝ × B → N} {δ : ℝ}
    (hδ : 0 < δ)
    (hloc : IsLocalHomeomorph (fun p : Ico 0 δ ×ˢ (univ : Set B) => F p.val))
    (hzero : Function.Injective (fun y => F (0, y))) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 ε ×ˢ (univ : Set B) => F p.val) := by
  let S := Ico 0 δ ×ˢ (univ : Set B)
  let f : S → N := fun p => F p.val
  let z : B → S := fun y => ⟨(0, y), ⟨⟨le_rfl, hδ⟩, mem_univ y⟩⟩
  have hz : Continuous z := (continuous_const.prodMk continuous_id).subtype_mk _
  have hi : InjOn f (range z) := by
    rintro p ⟨y, rfl⟩ q ⟨w, rfl⟩ hpq
    exact congrArg z (hzero hpq)
  obtain ⟨V, hVo, hKV, hVi⟩ := hi.exists_isOpen_superset (isCompact_range hz)
    (fun p _ => hloc.continuous.continuousAt) (by
      intro p _
      obtain ⟨U, hU, he⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hloc p
      refine ⟨U, hU, ?_⟩
      intro p hp q hq hpq
      have heq : (⟨p, hp⟩ : U) = ⟨q, hq⟩ := he.injective hpq
      exact congrArg Subtype.val heq)
  let H : (Ico (0 : ℝ) δ) × B ≃ₜ S :=
    (Homeomorph.refl (Ico (0 : ℝ) δ) |>.prodCongr (Homeomorph.Set.univ B)).symm.trans
      (Homeomorph.Set.prod (Ico 0 δ) (univ : Set B)).symm
  let t0 : Ico (0 : ℝ) δ := ⟨0, le_rfl, hδ⟩
  have hsub : ({t0} : Set (Ico (0 : ℝ) δ)) ×ˢ (univ : Set B) ⊆ H ⁻¹' V := by
    rintro ⟨t, y⟩ ⟨ht, _⟩
    have ht0 : t = t0 := ht
    subst t
    exact hKV ⟨y, rfl⟩
  obtain ⟨P, Q, hPo, _, htP, hBQ, hPQ⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_univ (hVo.preimage H.continuous) hsub
  obtain ⟨r, hr, hrP⟩ := Metric.mem_nhds_iff.mp (hPo.mem_nhds (htP (mem_singleton _)))
  let ε := min r δ / 2
  have hε : 0 < ε := half_pos (lt_min hr hδ)
  have hεδ : ε < δ := (half_lt_self (lt_min hr hδ)).trans_le (min_le_right _ _)
  have hεr : ε < r := (half_lt_self (lt_min hr hδ)).trans_le (min_le_left _ _)
  have hs : Ico 0 ε ×ˢ (univ : Set B) ⊆ S :=
    fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hεδ⟩, hp.2⟩
  have hsV : ∀ p : Ico 0 ε ×ˢ (univ : Set B), Set.inclusion hs p ∈ V := by
    intro p
    change H ((⟨p.val.1, (hs p.property).1⟩ : Ico (0 : ℝ) δ), p.val.2) ∈ V
    apply hPQ
    exact ⟨hrP (by
        change dist p.val.1 (0 : ℝ) < r
        rw [Real.dist_eq, sub_zero, abs_of_nonneg p.property.1.1]
        exact p.property.1.2.trans hεr), hBQ (mem_univ _)⟩
  have hso : IsOpen (Subtype.val ⁻¹' (Ico 0 ε ×ˢ (univ : Set B)) : Set S) := by
    have : (Subtype.val ⁻¹' (Ico 0 ε ×ˢ (univ : Set B)) : Set S) =
        {p : S | p.val.1 < ε} := by
      ext p
      exact ⟨fun h => h.1.2, fun h => ⟨⟨p.property.1.1, h⟩, mem_univ _⟩⟩
    rw [this]
    exact isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const
  have hinc := Topology.IsOpenEmbedding.inclusion hs hso
  refine ⟨ε, hε, hεδ.le, ?_⟩
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hloc.continuous.comp hinc.continuous)
    (fun p q hpq => hinc.injective (hVi (hsV p) (hsV q) hpq))
    (hloc.isOpenMap.comp hinc.isOpenMap)

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Actual local collars of one native field assemble into a single
positive-width collar of the compact intrinsic boundary. The overlap
identities are proved from the field's local coefficient extensions.
Joint smoothness, the native ODE, exact seam and boundary criterion, and
global open embedding all concern the same constructed map. -/
theorem exists_uniform_native_collar_of_local_collars
    [CompactSpace (IntrinsicBoundary.Point k M)]
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hcoeff : ∀ x : M,
      ∃ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
        e ∈ atlas (EuclideanHalfSpace (k + 1)) M ∧ x ∈ e.source ∧
        ∃ (f : Model (k + 1) → Model (k + 1)) (U : Set (Model (k + 1))),
          IsOpen U ∧ ContDiffOn ℝ ∞ f U ∧ e.extend (𝓡∂ (k + 1)) x ∈ U ∧
          ∀ y ∈ e.source, e.extend (𝓡∂ (k + 1)) y ∈ U →
            f (e.extend (𝓡∂ (k + 1)) y) =
              mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
                (e.extend (𝓡∂ (k + 1))) y (Z y))
    (hlocal : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (U : Set (IntrinsicBoundary.Point k M)) (δ : ℝ)
        (γ : ℝ × IntrinsicBoundary.Point k M → M),
        IsOpen U ∧ x ∈ U ∧ 0 < δ ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ γ
          (Ico 0 δ ×ˢ U) ∧
        Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ U => γ p.val) ∧
        (∀ y ∈ U, γ (0, y) = y.val) ∧
        (∀ y ∈ U, IsMIntegralCurveOn (fun t => γ (t, y)) Z (Ico 0 δ)) ∧
        (∀ y ∈ U, ∀ t ∈ Ico 0 δ,
          ((𝓡∂ (k + 1)).IsBoundaryPoint (γ (t, y)) ↔ t = 0)) ∧
        ∀ p ∈ Ico 0 δ ×ˢ U, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
          ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (γ p) ∧
          ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ U] p, g (γ q) = q) :
    ∃ (C : ℝ × IntrinsicBoundary.Point k M → M) (δ : ℝ), 0 < δ ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
        (Ico 0 δ ×ˢ univ) ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => C p.val) ∧
      (∀ y, C (0, y) = y.val) ∧
      (∀ y, IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ)) ∧
      (∀ y, ∀ t ∈ Ico 0 δ,
        ((𝓡∂ (k + 1)).IsBoundaryPoint (C (t, y)) ↔ t = 0)) ∧
      ∀ p ∈ Ico 0 δ ×ˢ univ, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C q) = q := by
  classical
  let B := IntrinsicBoundary.Point k M
  choose U d c hU hxU hd hc he hz hode hb hinv using hlocal
  obtain ⟨s, δ, hδ, hδd, hcov⟩ := exists_pos_finite_subcover U hU
    (fun x => ⟨x, hxU x⟩) d hd
  choose r hrs hrU using hcov
  have hcover (y : B) : ∃ i ∈ s, y ∈ U i := ⟨r y, hrs y, hrU y⟩
  let C : ℝ × B → M := fun p => c (r p.2) p
  have hsub (i : B) (hi : i ∈ s) : Ico 0 δ ⊆ Ico 0 (d i) :=
    fun _ ht => ⟨ht.1, ht.2.trans_le (hδd i hi)⟩
  have heq (i : B) (hi : i ∈ s) : EqOn C (c i) (Ico 0 δ ×ˢ U i) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact eqOn_of_native_integralCurveOn hcoeff
      (hode (r y) y (hrU y)) (hode i y hy)
      ((hz (r y) y (hrU y)).trans (hz i y hy).symm)
      (show t ∈ Ico 0 (min (d (r y)) (d i)) from
        ⟨ht.1, lt_min (ht.2.trans_le (hδd (r y) (hrs y)))
          (ht.2.trans_le (hδd i hi))⟩)
  have hCs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
      (Ico 0 δ ×ˢ (univ : Set B)) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := hcover p.2
    have hpU : p ∈ Ico 0 δ ×ˢ U i := ⟨hp.1, hpi⟩
    have hne : Ico 0 δ ×ˢ U i ∈ 𝓝[Ico 0 δ ×ˢ (univ : Set B)] p := by
      have hn : Prod.snd ⁻¹' U i ∈ 𝓝[Ico 0 δ ×ˢ (univ : Set B)] p := mem_nhdsWithin_of_mem_nhds
        ((hU i).preimage continuous_snd |>.mem_nhds hpi)
      exact mem_of_superset (inter_mem self_mem_nhdsWithin hn)
        (fun q hq => ⟨hq.1.1, hq.2⟩)
    have hsmooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
        (Ico 0 δ ×ˢ U i) :=
      ((hc i).mono (fun q hq => ⟨hsub i hi hq.1, hq.2⟩)).congr (heq i hi)
    exact (hsmooth p hpU).mono_of_mem_nhdsWithin hne
  have hzero (y : B) : C (0, y) = y.val := hz (r y) y (hrU y)
  have hCeq (y : B) : IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ) :=
    (hode (r y) y (hrU y)).mono (hsub (r y) (hrs y))
  have hCboundary (y : B) (t : ℝ) (ht : t ∈ Ico 0 δ) :
      ((𝓡∂ (k + 1)).IsBoundaryPoint (C (t, y)) ↔ t = 0) :=
    hb (r y) y (hrU y) t (hsub (r y) (hrs y) ht)
  have hCinv (p : ℝ × B) (hp : p ∈ Ico 0 δ ×ˢ univ) :
      ∃ g : M → ℝ × B,
        ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C q) = q := by
    let i := r p.2
    have hi : i ∈ s := hrs p.2
    have hpi : p.2 ∈ U i := hrU p.2
    have hpU : p ∈ Ico 0 δ ×ˢ U i := ⟨hp.1, hpi⟩
    obtain ⟨g, hg, hgi⟩ := hinv i p ⟨hsub i hi hp.1, hpi⟩
    have hne : Ico 0 δ ×ˢ U i ∈ 𝓝[Ico 0 δ ×ˢ (univ : Set B)] p := by
      have hn : Prod.snd ⁻¹' U i ∈ 𝓝[Ico 0 δ ×ˢ (univ : Set B)] p :=
        mem_nhdsWithin_of_mem_nhds ((hU i).preimage continuous_snd |>.mem_nhds hpi)
      exact mem_of_superset (inter_mem self_mem_nhdsWithin hn)
        (fun q hq => ⟨hq.1.1, hq.2⟩)
    have hle : 𝓝[Ico 0 δ ×ˢ (univ : Set B)] p ≤ 𝓝[Ico 0 (d i) ×ˢ U i] p :=
      (nhdsWithin_le_of_mem hne).trans (nhdsWithin_mono p
        (fun q hq => ⟨hsub i hi hq.1, hq.2⟩))
    refine ⟨g, ?_, ?_⟩
    · rwa [heq i hi hpU]
    · filter_upwards [hgi.filter_mono hle, hne] with q hq hqU
      rw [heq i hi hqU]
      exact hq
  have hCloc : IsLocalHomeomorph (fun p : Ico 0 δ ×ˢ (univ : Set B) => C p.val) := by
    apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
    intro p
    obtain ⟨i, hi, hpi⟩ := hcover p.val.2
    let S := Ico 0 δ ×ˢ (univ : Set B)
    let W : Set S := {q | q.val.2 ∈ U i}
    have hWo : IsOpen W := (hU i).preimage (continuous_snd.comp continuous_subtype_val)
    have hpW : p ∈ W := hpi
    let a : W → Ico 0 (d i) ×ˢ U i := fun q =>
      ⟨q.val.val, hsub i hi q.val.property.1, q.property⟩
    have ha : Topology.IsOpenEmbedding a := by
      have hb0 : Topology.IsEmbedding (fun q : W => q.val.val) :=
        Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
      have hb : Topology.IsEmbedding a :=
        hb0.codRestrict (Ico 0 (d i) ×ˢ U i)
          (fun q => ⟨hsub i hi q.val.property.1, q.property⟩)
      refine ⟨hb, ?_⟩
      have hrange : range a = {q : Ico 0 (d i) ×ˢ U i | q.val.1 < δ} := by
        ext q
        constructor
        · rintro ⟨w, rfl⟩
          exact w.val.property.1.2
        · intro hq
          refine ⟨⟨⟨q.val, ⟨q.property.1.1, hq⟩, mem_univ _⟩, q.property.2⟩, ?_⟩
          rfl
      rw [hrange]
      exact isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const
    refine ⟨W, hWo.mem_nhds hpW, ?_⟩
    have HH := (he i).comp ha
    convert HH using 1
    funext q
    exact heq i hi ⟨q.val.property.1, q.property⟩
  obtain ⟨ε, hε, hεδ, hemb⟩ := exists_pos_openEmbedding_of_localHomeomorph hδ hCloc
    (fun y w hyw => Subtype.ext (by simpa only [hzero] using hyw))
  have hsε : Ico 0 ε ⊆ Ico 0 δ := fun _ ht => ⟨ht.1, ht.2.trans_le hεδ⟩
  refine ⟨C, ε, hε, hCs.mono (fun p hp => ⟨hsε hp.1, hp.2⟩), hemb,
    hzero, fun y => (hCeq y).mono hsε, fun y t ht => hCboundary y t (hsε ht), ?_⟩
  intro p hp
  obtain ⟨g, hg, hgi⟩ := hCinv p ⟨hsε hp.1, hp.2⟩
  have hsεprod : Ico 0 ε ×ˢ (univ : Set B) ⊆ Ico 0 δ ×ˢ univ :=
    fun q hq => ⟨hsε hq.1, hq.2⟩
  exact ⟨g, hg, hgi.filter_mono (nhdsWithin_mono p hsεprod)⟩

/-- Source-local smooth scalar extensions and strict inwardness construct
a uniform native collar. Neither local collars, overlap identities,
global injectivity nor inverse germs are inputs. The scalar extension
convention is stated in every native atlas chart; inwardness is measured
in the preferred restricted chart at each boundary point. -/
theorem exists_uniform_native_collar_of_scalar_extensions
    [CompactSpace (IntrinsicBoundary.Point k M)]
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hscalar : ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
      e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ x ∈ e.source,
      ∀ i : Fin (k + 1),
        ∃ (f : Model (k + 1) → ℝ) (V : Set (Model (k + 1))),
          IsOpen V ∧ e.extend (𝓡∂ (k + 1)) x ∈ V ∧ ContDiffOn ℝ ∞ f V ∧
          f =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target] (e.extend (𝓡∂ (k + 1)) x)]
            (fun y => (show Model (k + 1) from
              mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
                (e.extend (𝓡∂ (k + 1))) ((e.extend (𝓡∂ (k + 1))).symm y)
                  (Z ((e.extend (𝓡∂ (k + 1))).symm y))) i))
    (hin : ∀ x : IntrinsicBoundary.Point k M,
      0 < (show Model (k + 1) from
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))) x.val
            (Z x.val)) 0) :
    ∃ (C : ℝ × IntrinsicBoundary.Point k M → M) (δ : ℝ), 0 < δ ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
        (Ico 0 δ ×ˢ univ) ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => C p.val) ∧
      (∀ y, C (0, y) = y.val) ∧
      (∀ y, IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ)) ∧
      (∀ y, ∀ t ∈ Ico 0 δ,
        ((𝓡∂ (k + 1)).IsBoundaryPoint (C (t, y)) ↔ t = 0)) ∧
      ∀ p ∈ Ico 0 δ ×ˢ univ, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C q) = q := by
  apply exists_uniform_native_collar_of_local_collars Z
  · intro x
    let e := chartAt (EuclideanHalfSpace (k + 1)) x
    have he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M := chart_mem_atlas _ x
    have hx : x ∈ e.source := mem_chart_source _ x
    obtain ⟨f, U, hU, hxU, hf, _, hfc⟩ :=
      exists_local_coefficients_of_scalar_extensions hx (hscalar e he x hx)
    refine ⟨e, he, hx, f, U, hU, hf, hxU, ?_⟩
    intro y hy hyU
    have h := hfc _ hyU (e y).property
    rw [(e.extend (𝓡∂ (k + 1))).left_inv
      (by simpa only [e.extend_source] using hy)] at h
    exact h
  · intro x
    let c := IntrinsicBoundary.chartAt x
    have hx : x ∈ c.chart.source := IntrinsicBoundary.mem_chartAt_source x
    have he : x.val ∈ c.ambient.source := by
      have h := hx
      rw [c.source_eq] at h
      exact h
    obtain ⟨γ, U, δ, hU, hxU, hδ, hγ, hemb, hinv, hzero, hode, hb⟩ :=
      exists_boundary_local_collar_of_scalar_extensions c hx Z
        (hscalar c.ambient c.mem_atlas x.val he) (hin x)
    exact ⟨U, δ, γ, hU, hxU, hδ, hγ, hemb, hzero, hode, hb, hinv⟩

end FsFltz.Geometry.IntrinsicCollar
