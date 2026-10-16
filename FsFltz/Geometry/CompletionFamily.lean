import FsFltz.Geometry.CompletionGluing
import FsFltz.Geometry.BoundaryNondegeneracy

/-!
# Joint regularity from compact and cylindrical completion formulas

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. The completed-family regularity conditions are
proved from jointly smooth compact coefficients and the cylindrical
`exp(r)` boundary formula on an open collar. Compatible real extensions
and collar-adapted compact presentations still have to be constructed.

The proof covers the completed space by the compact interior and an open
cylindrical collar. On the interior the inverse of the inclusion transports
the compact one-form family. On the collar the inverse cylinder coordinates
express the completed form as `exp(r)` times the pullback of the boundary
family. The chain rule and smoothness of fixed local inverse derivatives
make both expressions jointly smooth. The open collar includes radius zero,
so the same cylindrical expression proves regularity across the seam.
Taking the union of these joint coordinate neighborhoods preserves actual
open extensions at interval endpoints, including on noncompact completions.
The final interval result applies directly to transported completed primitives
of independently given domain families; it assumes compatible raw extensions,
not their completed smoothness and not a `PairDeformation` containing it.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

/-- Local open extensions assemble to a smooth neighborhood of the parameter
interval, without a uniform time margin on a noncompact spatial domain. -/
theorem smoothNearInterval_of_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Set E) (f : ℝ × E → F)
    (h : ∀ p ∈ parameterInterval ×ˢ s,
      ∃ U : Set (ℝ × E), IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ f U) :
    SmoothNearInterval s f := by
  let U := ⋃ (V : Set (ℝ × E)) (_ : IsOpen V ∧ ContDiffOn ℝ ∞ f V), V
  refine ⟨U, isOpen_iUnion (fun V => isOpen_iUnion (fun hV => hV.1)), ?_, ?_⟩
  · intro p hp
    obtain ⟨V, hV, hpV, hfV⟩ := h p hp
    exact mem_iUnion.mpr ⟨V, mem_iUnion.mpr ⟨⟨hV, hfV⟩, hpV⟩⟩
  · intro p hp
    change p ∈ ⋃ (V : Set (ℝ × E)) (_ : IsOpen V ∧ ContDiffOn ℝ ∞ f V), V at hp
    simp only [mem_iUnion] at hp
    obtain ⟨V, hV, hpV⟩ := hp
    exact (hV.2.contDiffAt (hV.1.mem_nhds hpV)).contDiffWithinAt

private theorem contDiffOn_oneForm_comp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set G} (a : G → F [⋀^Fin 1]→L[ℝ] ℝ) (B : G → E →L[ℝ] F)
    (ha : ContDiffOn ℝ ∞ a U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun z => (a z).compContinuousLinearMap (B z)) U := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := eE.contDiff.comp_contDiffOn
    ((eF.symm.contDiff.comp_contDiffOn ha).clm_comp hB)
  convert hs using 1
  ext z vs
  change a z (fun i => B z (vs i)) = a z (fun _ => B z (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

namespace SmoothManifold

/-- Pulling a jointly smooth one-form family through a fixed map which is
smooth only locally gives jointly smooth coefficients on that local patch.
The resulting pullback family's regularity is proved by the chain rule. -/
theorem local_formFamily_pullback {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (α : ℝ → N.Form 1) (hα : N.IsSmoothFormFamily α)
    (f : M.Point → N.Point) (V : Set M.Point) (hV : IsOpen V)
    (hf : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f V)
    (a : M.Point) (t : ℝ) (ht : t ∈ parameterInterval)
    (y : Model d) (hy : y ∈ (chartAt (Model d) a).target)
    (hx : (chartAt (Model d) a).symm y ∈ V) :
    ∃ U : Set (ℝ × Model d), IsOpen U ∧ (t, y) ∈ U ∧
      ContDiffOn ℝ ∞
        (fun q => M.formInChart a (M.pullback N f (α q.1)) q.2) U := by
  let c := chartAt (Model d) a
  let b := chartAt (Model e) (f (c.symm y))
  let W := c.target ∩ c.symm ⁻¹' V
  have hW : IsOpen W := c.continuousOn_symm.isOpen_inter_preimage c.open_target hV
  have hfW : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ (f ∘ c.symm) W :=
    hf.comp ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).mono
      inter_subset_left) inter_subset_right
  let S := W ∩ (f ∘ c.symm) ⁻¹' b.source
  have hS : IsOpen S := hfW.continuousOn.isOpen_inter_preimage hW b.open_source
  have hyS : y ∈ S := ⟨⟨hy, hx⟩, mem_chart_source _ _⟩
  let g := b ∘ f ∘ c.symm
  have hg : ContDiffOn ℝ ∞ g S :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := f (c.symm y))).comp
      (hfW.mono inter_subset_left) inter_subset_right).contDiffOn
  obtain ⟨A, hA, hcover, hcoeff⟩ := hα (f (c.symm y))
  let q : ℝ × Model d → ℝ × Model e := fun p => (p.1, g p.2)
  have hq : ContDiffOn ℝ ∞ q (univ ×ˢ S) :=
    contDiffOn_fst.prodMk (hg.comp contDiffOn_snd (fun _ hp => hp.2))
  let U := (univ ×ˢ S) ∩ q ⁻¹' A
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod hS) hA
  have hpU : (t, y) ∈ U :=
    ⟨⟨mem_univ _, hyS⟩, hcover ⟨ht, b.map_source (mem_chart_source _ _)⟩⟩
  have hcoeff' := hcoeff.comp (hq.mono inter_subset_left) inter_subset_right
  have hder : ContDiffOn ℝ ∞ (fun p : ℝ × Model d => fderiv ℝ g p.2) U :=
    (hg.fderiv_of_isOpen (m := ∞) hS (by simp)).comp contDiffOn_snd
      (fun _ hp => hp.1.2)
  refine ⟨U, hU, hpU, (contDiffOn_oneForm_comp _ _ hcoeff' hder).congr ?_⟩
  intro p hp
  exact M.formInChart_pullback N (α p.1) a (f (c.symm y)) p.2 hp.1.2.1.1 hp.1.2.2
    ((hf.contMDiffAt (hV.mem_nhds hp.1.2.1.2)).mdifferentiableAt (by simp))

/-- A fixed smooth scalar times a local pullback preserves joint one-form
regularity on an open patch in time and space. -/
theorem local_formFamily_scaled {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (η : ℝ → M.Form 1) (α : ℝ → N.Form 1) (hα : N.IsSmoothFormFamily α)
    (f : M.Point → N.Point) (ρ : M.Point → ℝ)
    (V : Set M.Point) (hV : IsOpen V)
    (hf : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f V)
    (hρ : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ V)
    (W : Set (ℝ × M.Point)) (hW : IsOpen W)
    (hWV : W ⊆ univ ×ˢ V)
    (heq : ∀ q ∈ W, η q.1 q.2 = ρ q.2 • M.pullback N f (α q.1) q.2)
    (a : M.Point) (t : ℝ) (ht : t ∈ parameterInterval)
    (y : Model d) (hy : y ∈ (chartAt (Model d) a).target)
    (hp : (t, (chartAt (Model d) a).symm y) ∈ W) :
    ∃ U : Set (ℝ × Model d), IsOpen U ∧ (t, y) ∈ U ∧
      ContDiffOn ℝ ∞ (fun q => M.formInChart a (η q.1) q.2) U := by
  let c := chartAt (Model d) a
  obtain ⟨A, hA, hpA, hcoeff⟩ := M.local_formFamily_pullback N α hα f V hV hf
    a t ht y hy (hWV hp).2
  let Q := c.target ∩ c.symm ⁻¹' V
  have hQ : IsOpen Q := c.continuousOn_symm.isOpen_inter_preimage c.open_target hV
  have hρQ : ContDiffOn ℝ ∞ (ρ ∘ c.symm) Q :=
    (hρ.comp ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).mono
      inter_subset_left) inter_subset_right).contDiffOn
  let q : ℝ × Model d → ℝ × M.Point := fun p => (p.1, c.symm p.2)
  have hq : ContinuousOn q (univ ×ˢ Q) :=
    continuousOn_fst.prodMk (c.continuousOn_symm.comp continuousOn_snd
      (fun _ hp => hp.2.1))
  let B := (univ ×ˢ Q) ∩ q ⁻¹' W
  have hB : IsOpen B := hq.isOpen_inter_preimage (isOpen_univ.prod hQ) hW
  have hpB : (t, y) ∈ B := ⟨⟨mem_univ _, ⟨hy, (hWV hp).2⟩⟩, hp⟩
  have hρ' : ContDiffOn ℝ ∞ (fun p : ℝ × Model d => ρ (c.symm p.2)) (A ∩ B) :=
    hρQ.comp contDiffOn_snd (fun _ hp => hp.2.1.2)
  refine ⟨A ∩ B, hA.inter hB, ⟨hpA, hpB⟩,
    (hρ'.smul (hcoeff.mono inter_subset_left)).congr ?_⟩
  intro p hp
  have he := heq (q p) hp.2.2
  unfold formInChart
  rw [he]
  rfl

/-- Pullback through a fixed smooth map preserves joint regularity of an
actual one-form family, including its open parameter endpoint extensions. -/
theorem isSmoothFormFamily_pullback_one {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (f : M.SmoothMap N)
    (α : ℝ → N.Form 1) (hα : N.IsSmoothFormFamily α) :
    M.IsSmoothFormFamily (fun t => M.pullback N f (α t)) := by
  intro a
  apply smoothNearInterval_of_local
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  exact M.local_formFamily_pullback N α hα f univ isOpen_univ f.contMDiff.contMDiffOn
    a t ht y hy (mem_univ _)

end SmoothManifold

namespace Completion

set_option backward.isDefEq.respectTransparency false in
private theorem localInverse_pullback_eq {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (f : M.SmoothMap N)
    (x : M.Point) (l : IsLocalDiffeomorphAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f x)
    (η : N.Form 1) (α : M.Form 1) (y : N.Point)
    (hy : y ∈ l.localInverse.source)
    (hα : M.pullback N f η (l.localInverse y) = α (l.localInverse y)) :
    η y = N.pullback M l.localInverse α y := by
  have hi := (l.localInverse_contMDiffOn.contMDiffAt
    (l.localInverse.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  have he : (f ∘ l.localInverse : N.Point → N.Point) =ᶠ[𝓝 y] id := by
    filter_upwards [l.localInverse.open_source.mem_nhds hy] with z hz
    exact l.localInverse_right_inv hz
  have hd : (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f (l.localInverse y)).comp
      (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) l.localInverse y) =
      ContinuousLinearMap.id ℝ (Model e) := by
    rw [← mfderiv_comp y (f.contMDiff.mdifferentiableAt (by simp)) hi,
      he.mfderiv_eq, mfderiv_id]
    rfl
  ext vs
  change η y vs = α (l.localInverse y) (fun i =>
    mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) l.localInverse y (vs i))
  rw [← hα]
  change η y vs = η (f (l.localInverse y)) (fun i =>
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f (l.localInverse y))
      ((mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) l.localInverse y) (vs i)))
  rw [l.localInverse_right_inv hy]
  congr 1
  funext i
  exact (congrArg (fun L => L (vs i)) hd).symm

set_option backward.isDefEq.respectTransparency false in
private theorem localInverse_endForm_eq {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (p : D.domain.boundary.Point × ℝ)
    (η : C.ambient.manifold.Form 1) (β : D.domain.boundary.Form 1)
    (z : C.ambient.manifold.Point)
    (hz : z ∈ (C.endMap_isLocalDiffeomorph p).localInverse.source)
    (hη : ∀ v s, evalOne η (C.endMap ((C.endMap_isLocalDiffeomorph p).localInverse z))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) C.endMap
        ((C.endMap_isLocalDiffeomorph p).localInverse z) (v, s)) =
      Real.exp ((C.endMap_isLocalDiffeomorph p).localInverse z).2 *
        evalOne β ((C.endMap_isLocalDiffeomorph p).localInverse z).1 v) :
    η z = Real.exp ((C.endMap_isLocalDiffeomorph p).localInverse z).2 •
      C.ambient.manifold.pullback D.domain.boundary
        (fun y => ((C.endMap_isLocalDiffeomorph p).localInverse y).1) β z := by
  let l := C.endMap_isLocalDiffeomorph p
  change z ∈ l.localInverse.source at hz
  change ∀ v s, evalOne η (C.endMap (l.localInverse z))
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      C.endMap (l.localInverse z) (v, s)) =
    Real.exp (l.localInverse z).2 * evalOne β (l.localInverse z).1 v at hη
  change η z = Real.exp (l.localInverse z).2 • C.ambient.manifold.pullback
    D.domain.boundary (fun y => (l.localInverse y).1) β z
  have hi := (l.localInverse_contMDiffOn.contMDiffAt
    (l.localInverse.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have he : (C.endMap ∘ l.localInverse : C.ambient.manifold.Point →
      C.ambient.manifold.Point) =ᶠ[𝓝 z] id := by
    filter_upwards [l.localInverse.open_source.mem_nhds hz] with y hy
    exact l.localInverse_right_inv hy
  have hd : (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      C.endMap (l.localInverse z)).comp
      (mfderiv 𝓘(ℝ, Model d) ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        l.localInverse z) = ContinuousLinearMap.id ℝ (Model d) := by
    rw [← mfderiv_comp z (C.smooth_endMap.mdifferentiableAt (by simp)) hi,
      he.mfderiv_eq, mfderiv_id]
    rfl
  have hfst := mfderiv_comp (g := Prod.fst) z mdifferentiableAt_fst hi
  rw [mfderiv_fst] at hfst
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (d - 1))
    (fun y => (l.localInverse y).1) z =
    (ContinuousLinearMap.fst ℝ (Model (d - 1)) ℝ).comp
      (mfderiv 𝓘(ℝ, Model d) ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        l.localInverse z) at hfst
  ext vs
  have hvs : vs = fun _ : Fin 1 => vs 0 := by
    funext i
    rw [Fin.eq_zero i]
  rw [hvs]
  have hh := hη
    ((mfderiv 𝓘(ℝ, Model d) ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      l.localInverse z (vs 0)).1)
    ((mfderiv 𝓘(ℝ, Model d) ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      l.localInverse z (vs 0)).2)
  have hdv := congrArg (fun L => L (vs 0)) hd
  change (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
    C.endMap (l.localInverse z))
      (mfderiv 𝓘(ℝ, Model d) ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        l.localInverse z (vs 0)) = vs 0 at hdv
  rw [Prod.eta, hdv] at hh
  change evalOne η z (vs 0) = Real.exp (l.localInverse z).2 *
    evalOne β (l.localInverse z).1
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (d - 1))
        (fun y => (l.localInverse y).1) z (vs 0))
  rw [hfst]
  let aη : C.ambient.manifold.Point → Model d [⋀^Fin 1]→L[ℝ] ℝ := η
  have hpoint := congrArg aη (l.localInverse_right_inv hz)
  change aη (C.endMap (l.localInverse z)) (fun _ => vs 0) = _ at hh
  rw [hpoint] at hh
  exact hh

/-- Compact joint smoothness and the `exp(r)` boundary formula on an open
parameter-dependent collar imply joint smoothness of a raw completed form
extension. No regularity of that completed extension is assumed.

The compact equation is required only on the interior; the open cylindrical
collar supplies the seam regularity. The hypotheses concern coefficient
extensions and their exact local equations;
constructing compatible extensions for an arbitrary geometric family remains
a separate obligation. The collar need not contain all negative radii. -/
theorem isSmoothFormFamily_of_compact_end {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (η : ℝ → C.ambient.manifold.Form 1)
    (α : ℝ → D.domain.extension.Form 1)
    (β : ℝ → D.domain.boundary.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hβ : D.domain.boundary.IsSmoothFormFamily β)
    (hcompact : ∀ t x, x ∈ interior D.domain.carrier →
      D.domain.extension.pullback C.ambient.manifold C.inclusion.map (η t) x = α t x)
    (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) (hU : IsOpen U)
    (hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U)
    (hend : ∀ q ∈ U, ∀ v s,
      evalOne (η q.1) (C.endMap q.2)
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap q.2 (v, s)) =
        Real.exp q.2.2 * evalOne (β q.1) q.2.1 v) :
    C.ambient.manifold.IsSmoothFormFamily η := by
  intro a
  apply smoothNearInterval_of_local
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  let c := chartAt (Model d) a
  let z := c.symm y
  by_cases hz : z ∈ C.inclusion.map '' interior D.domain.carrier
  · obtain ⟨x, hx, hix⟩ := hz
    let l := C.inclusion_isLocalDiffeomorph x
    let V := l.localInverse.source ∩ l.localInverse ⁻¹' interior D.domain.carrier
    have hV : IsOpen V := l.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      l.localInverse.open_source isOpen_interior
    have hzV : z ∈ V := by
      rw [← hix]
      exact ⟨l.localInverse_mem_source, by
        change l.localInverse (C.inclusion.map x) ∈ interior D.domain.carrier
        simpa only [l.localInverse_left_inv l.localInverse_mem_target] using hx⟩
    apply C.ambient.manifold.local_formFamily_scaled D.domain.extension η α hα
      l.localInverse (fun _ => 1) V hV
      (l.localInverse_contMDiffOn.mono inter_subset_left) contMDiffOn_const
      (univ ×ˢ V) (isOpen_univ.prod hV) (Subset.rfl) _ a t ht y hy ⟨mem_univ _, hzV⟩
    intro q hq
    simp only [one_smul]
    exact localInverse_pullback_eq D.domain.extension C.ambient.manifold C.inclusion.map
      x l (η q.1) (α q.1) q.2 hq.2.1 (hcompact q.1 _ hq.2.2)
  · have hz' : z ∈ range (fun p : D.domain.boundary.Point × Ici (0 : ℝ) =>
        C.endMap (p.1, p.2)) := by
      rw [C.range_nonnegative_endMap]
      exact hz
    obtain ⟨⟨x, ⟨r, hr⟩⟩, hxr⟩ := hz'
    let l := C.endMap_isLocalDiffeomorph (x, r)
    let V := l.localInverse.source
    let q : ℝ × C.ambient.manifold.Point → ℝ × (D.domain.boundary.Point × ℝ) :=
      fun p => (p.1, l.localInverse p.2)
    have hq : ContinuousOn q (univ ×ˢ V) :=
      continuousOn_fst.prodMk (l.localInverse_contMDiffOn.continuousOn.comp
        continuousOn_snd (fun _ hp => hp.2))
    let W := (univ ×ˢ V) ∩ q ⁻¹' U
    have hW : IsOpen W := hq.isOpen_inter_preimage
      (isOpen_univ.prod l.localInverse.open_source) hU
    have hzW : (t, z) ∈ W := by
      rw [← hxr]
      exact ⟨⟨mem_univ _, l.localInverse_mem_source⟩, by
        change (t, l.localInverse (C.endMap (x, r))) ∈ U
        rw [l.localInverse_left_inv l.localInverse_mem_target]
        exact hpos ⟨ht, ⟨mem_univ _, hr⟩⟩⟩
    have hf := contMDiff_fst.comp_contMDiffOn l.localInverse_contMDiffOn
    have hρ := Real.contDiff_exp.contMDiff.comp_contMDiffOn
      (contMDiff_snd.comp_contMDiffOn l.localInverse_contMDiffOn)
    apply C.ambient.manifold.local_formFamily_scaled D.domain.boundary η β hβ
      (fun p => (l.localInverse p).1) (fun p => Real.exp (l.localInverse p).2)
      V l.localInverse.open_source hf hρ W hW inter_subset_left _ a t ht y hy hzW
    intro p hp
    exact C.localInverse_endForm_eq (x, r) (η p.1) (β p.1) p.2 hp.1.2
      (hend (q p) hp.2)

/-- The boundary coefficient family is the actual restriction of the compact
primitive family; its joint smoothness is obtained by pullback. -/
theorem isSmoothFormFamily_of_compact_boundary {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (η : ℝ → C.ambient.manifold.Form 1)
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hcompact : ∀ t x, x ∈ interior D.domain.carrier →
      D.domain.extension.pullback C.ambient.manifold C.inclusion.map (η t) x = α t x)
    (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) (hU : IsOpen U)
    (hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U)
    (hend : ∀ q ∈ U, ∀ v s,
      evalOne (η q.1) (C.endMap q.2)
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap q.2 (v, s)) = Real.exp q.2.2 *
          evalOne (D.domain.boundaryForm (α q.1)) q.2.1 v) :
    C.ambient.manifold.IsSmoothFormFamily η :=
  C.isSmoothFormFamily_of_compact_end η α (fun t => D.domain.boundaryForm (α t))
    hα (D.domain.boundary.isSmoothFormFamily_pullback_one D.domain.extension
      D.domain.boundaryInclusion.map α hα) hcompact U hU hpos hend

/-- This proves precisely the completed primitive regularity clause needed
for a domain family presented on a fixed completion. The input contains
independent domains, completions and their presentation maps, together with
raw compatible coefficient extensions; it does not contain the completed
regularity conclusion or a deformation already asserting that conclusion. -/
theorem isSmoothIntervalFormFamily_pullback_of_compact_boundary
    {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (η : ℝ → C.ambient.manifold.Form 1)
    (hη : ∀ t : Parameter, η t.val =
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive)
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hcompact : ∀ t x, x ∈ D.domain.carrier →
      D.domain.extension.pullback C.ambient.manifold C.inclusion.map (η t) x = α t x)
    (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) (hU : IsOpen U)
    (hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U)
    (hend : ∀ q ∈ U, ∀ v s,
      evalOne (η q.1) (C.endMap q.2)
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap q.2 (v, s)) = Real.exp q.2.2 *
          evalOne (D.domain.boundaryForm (α q.1)) q.2.1 v) :
    C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive) :=
  ⟨η, C.isSmoothFormFamily_of_compact_boundary η α hα
    (fun t x hx => hcompact t x (interior_subset hx)) U hU hpos hend, hη⟩

end Completion
end FsFltz.Geometry
