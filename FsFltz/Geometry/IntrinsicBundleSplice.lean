import FsFltz.Geometry.IntrinsicBundleGauge
import FsFltz.Geometry.IntrinsicBundleTransition

/-!
# Smooth compatibility of corrected and spliced bundle charts

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. The topological splice is proved compatible with the smooth
bundle atlas in both directions using actual joint open germs. This is
a foundation for trivializing compact parameter bundles, not a geometric
comparison chain or a completion correspondence.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {d : ℕ} {H F : Type*} [TopologicalSpace H] [TopologicalSpace F]
  {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H F]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace F E)] [SmoothCompactBundle I (F := F) E]

/-- The corrected chart transition from an arbitrary chart is the actual
original transition followed by the smooth correction. -/
theorem coordChange_gaugeTrivialization (e e' e₀ : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet)
    {t : Parameter} (ht₀ : t ∈ e₀.baseSet) (ht : t ∈ e.baseSet) (x : F) :
    e₀.coordChange (gaugeTrivialization e e' he he' σ hσ hoverlap) t x =
      e.coordChange e' (σ t.val) (e₀.coordChange e t x) := by
  have hp : (e₀.toOpenPartialHomeomorph.symm (t, x)).proj = t :=
    e₀.proj_symm_apply' ht₀
  have hpe : (e₀.toOpenPartialHomeomorph.symm (t, x)).proj ∈ e.baseSet := by
    rw [hp]; exact ht
  change (gaugeTrivialization e e' he he' σ hσ hoverlap
    (e₀.toOpenPartialHomeomorph.symm (t, x))).2 = _
  rw [gaugeTrivialization_apply]
  rw [e.coe_fst' hpe, hp]
  rfl

/-- The inverse corrected-chart transition uses the reversed correction
at the same parameter, followed by the original transition. -/
theorem gaugeTrivialization_coordChange (e e' e₀ : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet) (t : Parameter) (x : F) :
    (gaugeTrivialization e e' he he' σ hσ hoverlap).coordChange e₀ t x =
      e.coordChange e₀ t (e'.coordChange e (σ t.val) x) := rfl

/-- Smooth gauge correction preserves compatibility with every original
atlas chart, in both directions. This composes open extension germs. -/
theorem gaugeTrivialization_compatible (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet) :
    CompatibleTrivialization I E (gaugeTrivialization e e' he he' σ hσ hoverlap) := by
  intro e₀ he₀
  constructor
  · have hf := (SmoothCompactBundle.smoothTransition e' he' e he).hasSmoothFamilyOn.reparam
      σ hσ (fun s => ⟨(hoverlap s).2, (hoverlap s).1⟩)
    have hg := (SmoothCompactBundle.smoothTransition e he e₀ he₀).hasSmoothFamilyOn
    have hc : Continuous (fun p : Parameter × F => e'.coordChange e (σ p.1.val) p.2) :=
      ((SmoothCompactBundle.smoothTransition e' he' e he).contMDiff_reparam σ hσ
        (fun s => ⟨(hoverlap s).2, (hoverlap s).1⟩)).continuous.comp
          (continuous_subtype_val.prodMap continuous_id)
    exact (hf.mono (subset_univ _)).comp (e.open_baseSet.inter e₀.open_baseSet)
      hg hc.continuousOn |>.congr
        (fun t _ x => (gaugeTrivialization_coordChange e e' e₀ he he' σ hσ hoverlap t x).symm)
  · have hf := (SmoothCompactBundle.smoothTransition e₀ he₀ e he).hasSmoothFamilyOn
    have hg := (SmoothCompactBundle.smoothTransition e he e' he').hasSmoothFamilyOn.reparam
      σ hσ hoverlap
    exact (hf.comp (e₀.open_baseSet.inter e.open_baseSet) (hg.mono (subset_univ _))
      (continuousOn_coordChange e₀ e)).congr
        (fun t ht x => (coordChange_gaugeTrivialization e e' e₀ he he' σ hσ hoverlap
          ht.1 ht.2 x).symm)

omit [∀ t, TopologicalSpace (E t)] [SmoothCompactBundle I (F := F) E] in
/-- Whole-fibre agreement of two charts determines their transitions
from another chart. -/
theorem coordChange_eq_of_eq_on_fiber (e e' e₀ : Trivialization F (π F E))
    {t : Parameter} (ht₀ : t ∈ e₀.baseSet)
    (heq : ∀ p : TotalSpace F E, p.proj = t → e p = e' p) (x : F) :
    e₀.coordChange e t x = e₀.coordChange e' t x :=
  congrArg Prod.snd (heq _ (e₀.proj_symm_apply' ht₀))

omit [∀ t, TopologicalSpace (E t)] [SmoothCompactBundle I (F := F) E] in
/-- Whole-fibre chart agreement also determines the inverse transition;
this uses actual chart inverses on their common native fibre. -/
theorem coordChange_eq_of_eq_on_fiber_left (e e' e₀ : Trivialization F (π F E))
    {t : Parameter} (ht : t ∈ e.baseSet) (ht' : t ∈ e'.baseSet)
    (heq : ∀ p : TotalSpace F E, p.proj = t → e p = e' p) (x : F) :
    e.coordChange e₀ t x = e'.coordChange e₀ t x := by
  have hp : (e.toOpenPartialHomeomorph.symm (t, x)).proj = t := e.proj_symm_apply' ht
  have hps : e.toOpenPartialHomeomorph.symm (t, x) ∈ e'.source := by
    rw [e'.mem_source, hp]; exact ht'
  have hval : e' (e.toOpenPartialHomeomorph.symm (t, x)) = (t, x) :=
    (heq _ hp).symm.trans (e.apply_symm_apply' ht)
  have hinv : e'.toOpenPartialHomeomorph.symm (t, x) =
      e.toOpenPartialHomeomorph.symm (t, x) := by
    calc
      _ = e'.toOpenPartialHomeomorph.symm
          (e' (e.toOpenPartialHomeomorph.symm (t, x))) := congrArg _ hval.symm
      _ = _ := e'.toOpenPartialHomeomorph.left_inv hps
  unfold Trivialization.coordChange
  rw [hinv]

/-- Compatibility is local in the base when the charts themselves agree
on whole native fibres. This treats forward and inverse transitions. -/
theorem compatibleTrivialization_of_locally_eq (e : Trivialization F (π F E))
    (h : ∀ t ∈ e.baseSet, ∃ (b : Trivialization F (π F E)) (Q : Set Parameter),
      CompatibleTrivialization I E b ∧ IsOpen Q ∧ t ∈ Q ∧
      ∀ s ∈ Q, s ∈ e.baseSet → s ∈ b.baseSet ∧
        ∀ p : TotalSpace F E, p.proj = s → e p = b p) :
    CompatibleTrivialization I E e := by
  intro e₀ he₀
  constructor
  · apply HasSmoothFamilyOn.of_locally
    intro t ht
    obtain ⟨b, Q, hb, hQ, htQ, heqb⟩ := h t ht.1
    refine ⟨Q, hQ, htQ, ?_⟩
    exact ((hb e₀ he₀).1.hasSmoothFamilyOn.mono (fun s hs =>
      ⟨(heqb s hs.2 hs.1.1).1, hs.1.2⟩)).congr (fun s hs x =>
        (coordChange_eq_of_eq_on_fiber_left e b e₀ hs.1.1
          (heqb s hs.2 hs.1.1).1 (heqb s hs.2 hs.1.1).2 x).symm)
  · apply HasSmoothFamilyOn.of_locally
    intro t ht
    obtain ⟨b, Q, hb, hQ, htQ, heqb⟩ := h t ht.2
    refine ⟨Q, hQ, htQ, ?_⟩
    exact ((hb e₀ he₀).2.hasSmoothFamilyOn.mono (fun s hs =>
      ⟨hs.1.1, (heqb s hs.2 hs.1.2).1⟩)).congr (fun s hs x =>
        (coordChange_eq_of_eq_on_fiber e b e₀ hs.1.1
          (heqb s hs.2 hs.1.2).2 x).symm)

/-- The existing gauge splice has both ordered joint extension germs
against every atlas chart. At the seam it is literally the left chart
on an open neighborhood; away from the seam it is one smooth branch. -/
theorem gaugeSpliceTrivialization_compatible (eL eR : Trivialization F (π F E))
    (heL : eL ∈ trivializationAtlas F E) (heR : eR ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ eR.baseSet ∩ eL.baseSet)
    (c : Parameter) (hcL : c ∈ eL.baseSet) (hcR : c ∈ eR.baseSet)
    (hσc : σ c.val = c) (hσnear : (fun s => (σ s).val) =ᶠ[𝓝 c.val] id) :
    CompatibleTrivialization I E
      (gaugeSpliceTrivialization eL eR heL heR σ hσ hoverlap c hcL hcR hσc) := by
  classical
  let T := gaugeSpliceTrivialization eL eR heL heR σ hσ hoverlap c hcL hcR hσc
  have hbase : T.baseSet = (Iic c).ite eL.baseSet eR.baseSet := rfl
  apply compatibleTrivialization_of_locally_eq
  intro t ht
  rcases lt_trichotomy t c with hlt | heq | hgt
  · refine ⟨eL, Iio c, compatibleTrivialization_of_mem heL, isOpen_Iio, hlt, ?_⟩
    intro s hs hsT
    have hsle : s ≤ c := le_of_lt hs
    have hsL : s ∈ eL.baseSet := by
      change s ∈ T.baseSet at hsT
      rw [hbase] at hsT
      simpa [Set.ite, hsle] using hsT
    refine ⟨hsL, ?_⟩
    intro p hp
    rw [gaugeSpliceTrivialization_apply, ite_eq_left (by rw [hp]; exact hsle)]
  · subst t
    have hnear := gaugeSpliceTrivialization_eventually_eq
      eL eR heL heR σ hσ hoverlap c hcL hcR hσc hσnear
    have hN : {s : Parameter | s ∈ eL.baseSet ∧
      ∀ p : TotalSpace F E, p.proj = s → T p = eL p} ∈ 𝓝 c := by
      filter_upwards [hnear, eL.open_baseSet.mem_nhds hcL] with s hs hsL
      exact ⟨hsL, hs⟩
    obtain ⟨Q, hQsub, hQ, hcQ⟩ := mem_nhds_iff.mp hN
    exact ⟨eL, Q, compatibleTrivialization_of_mem heL, hQ, hcQ,
      fun s hs _ => hQsub hs⟩
  · refine ⟨gaugeTrivialization eR eL heR heL σ hσ hoverlap, Ioi c,
      gaugeTrivialization_compatible eR eL heR heL σ hσ hoverlap,
      isOpen_Ioi, hgt, ?_⟩
    intro s hs hsT
    have hsnle : ¬s ≤ c := not_le.mpr hs
    have hsR : s ∈ eR.baseSet := by
      change s ∈ T.baseSet at hsT
      rw [hbase] at hsT
      simpa [Set.ite, hsnle] using hsT
    refine ⟨hsR, ?_⟩
    intro p hp
    rw [gaugeSpliceTrivialization_apply, ite_eq_right (by rw [hp]; exact hsnle)]

/-- Compatible charts, including charts constructed by previous splices,
admit a new actual smooth splice. The correction is constructed from the
open overlap, and the result is compatible with the original atlas. -/
theorem exists_compatible_gaugeSpliceTrivialization
    (eL eR : Trivialization F (π F E))
    (heL : CompatibleTrivialization I E eL) (heR : CompatibleTrivialization I E eR)
    (c : Parameter) (hcL : c ∈ eL.baseSet) (hcR : c ∈ eR.baseSet)
    (hc0 : 0 < c.val) (hc1 : c.val < 1) :
    ∃ σ : ℝ → Parameter, ContDiff ℝ ∞ (fun s => (σ s).val) ∧
      (∀ s, σ s ∈ eR.baseSet ∩ eL.baseSet) ∧
      ∃ T : Trivialization F (π F E), CompatibleTrivialization I E T ∧
        T.baseSet = (Iic c).ite eL.baseSet eR.baseSet ∧
        (∀ p : TotalSpace F E, T p = if p.proj ≤ c then eL p else
          ((eR p).1, eR.coordChange eL (σ (eR p).1.val) (eR p).2)) ∧
        ∀ᶠ t in 𝓝 c, ∀ p : TotalSpace F E, p.proj = t → T p = eL p := by
  have hseed : ∀ e₀ ∈ trivializationAtlas F E, CompatibleTrivialization I E e₀ :=
    fun _ he₀ => compatibleTrivialization_of_mem he₀
  obtain ⟨σ, hσ, hoverlap, hnear, _⟩ := exists_smooth_reparam_in_open
    (eR.open_baseSet.inter eL.open_baseSet) c ⟨hcR, hcL⟩ hc0 hc1
  have hσc : σ c.val = c := Subtype.ext hnear.eq_of_nhds
  let : SmoothCompactBundle I (F := F) E := compatibleSmoothCompactBundle
  have hL : eL ∈ trivializationAtlas F E := heL
  have hR : eR ∈ trivializationAtlas F E := heR
  let T := gaugeSpliceTrivialization eL eR hL hR σ hσ hoverlap c hcL hcR hσc
  have hT := gaugeSpliceTrivialization_compatible
    eL eR hL hR σ hσ hoverlap c hcL hcR hσc hnear
  refine ⟨σ, hσ, hoverlap, T, ?_, rfl, ?_, ?_⟩
  · intro e₀ he₀
    exact hT e₀ (hseed e₀ he₀)
  · intro p
    rw [gaugeSpliceTrivialization_apply, gaugeTrivialization_apply]
  · exact gaugeSpliceTrivialization_eventually_eq
      eL eR hL hR σ hσ hoverlap c hcL hcR hσc hnear

/-- Closure under smooth splicing in the form used by interval
globalization: both compatibility and the literal enlarged base set. -/
theorem exists_compatible_splice (eL eR : Trivialization F (π F E))
    (heL : CompatibleTrivialization I E eL) (heR : CompatibleTrivialization I E eR)
    (c : Parameter) (hcL : c ∈ eL.baseSet) (hcR : c ∈ eR.baseSet)
    (hc0 : 0 < c.val) (hc1 : c.val < 1) :
    ∃ T : Trivialization F (π F E), CompatibleTrivialization I E T ∧
      T.baseSet = (Iic c).ite eL.baseSet eR.baseSet := by
  obtain ⟨_, _, _, T, hT, hbase, _⟩ :=
    exists_compatible_gaugeSpliceTrivialization eL eR heL heR c hcL hcR hc0 hc1
  exact ⟨T, hT, hbase⟩

end FsFltz.Geometry.IntrinsicSmoothBundle
