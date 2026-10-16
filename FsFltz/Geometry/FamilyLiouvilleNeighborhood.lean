import FsFltz.Geometry.FamilyLiouville
import FsFltz.Geometry.Liouville
import FsFltz.Geometry.VectorFieldBridge

/-!
# A common nondegeneracy neighborhood for varying Liouville primitives

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and `sec:lean`,
lines 783–814. Joint smoothness of the primitive is the input. The canonical
contraction field is constructed on an actual open subset of parameter times
extension space containing the entire compact family. Neither symplecticity
outside the parameter interval nor joint smoothness of the supplied fields
is assumed. This is a producer for the family local-flow construction;
it constructs no collar or completion.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- Smooth canonical chart coefficients give a native smooth tangent vector
along the spatial projection of the parameter product. -/
theorem contMDiffAt_familySection_of_chart {d : ℕ} (M : SmoothManifold d)
    (Z : (t : ℝ) → (x : M.Point) → M.Tangent x)
    (a : M.Point) (p : ℝ × M.Point)
    (hp : p.2 ∈ (chartAt (Model d) a).source)
    (hZ : ContDiffAt ℝ ∞ (fun ty : ℝ × Model d =>
      M.vectorInChart a (Z ty.1) ty.2) (p.1, chartAt (Model d) a p.2)) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun q : ℝ × M.Point =>
        (⟨q.2, Z q.1 q.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) p := by
  let c := chartAt (Model d) a
  let e := trivializationAt (Model d) (TangentSpace (𝓘(ℝ, Model d))) a
  have he : (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point) ∈ e.source := hp
  apply (e.contMDiffAt_iff
    (f := fun q : ℝ × M.Point =>
      (⟨q.2, Z q.1 q.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point))
    (IM := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (IB := 𝓘(ℝ, Model d)) he).mpr
  refine ⟨contMDiffAt_snd, ?_⟩
  have hc : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c p.2 :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := a)).contMDiffAt
      (c.open_source.mem_nhds hp)
  have hchart : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, ℝ × Model d) ∞ (fun q : ℝ × M.Point => (q.1, c q.2)) p :=
    (contMDiffAt_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, Model d))).prodMk_space
      (hc.comp p (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, Model d))))
  apply (hZ.contMDiffAt.comp p hchart).congr_of_eventuallyEq
  have hsnd : Continuous (Prod.snd : ℝ × M.Point → M.Point) := continuous_snd
  filter_upwards [hsnd.continuousAt.preimage_mem_nhds
    (c.open_source.mem_nhds hp)] with q hq
  dsimp only [Function.comp_def, vectorInChart]
  rw [c.left_inv hq]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := ℝ) e hq]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- At every interval parameter and nondegenerate spatial point, smooth
primitive coefficients produce an open product neighborhood on which the
actual differential stays nondegenerate and its canonical field is jointly
smooth as a native tangent-bundle map. -/
theorem exists_liouvilleVector_family_neighborhood_at {d : ℕ} (M : SmoothManifold d)
    (alpha : ℝ → M.Form 1) (halpha : M.IsSmoothFormFamily alpha)
    (p : ℝ × M.Point) (ht : p.1 ∈ parameterInterval)
    (hnd : M.Nondegenerate (M.exteriorDerivative (alpha p.1)) p.2) :
    ∃ V : Set (ℝ × M.Point), IsOpen V ∧ p ∈ V ∧
      (∀ q ∈ V, M.Nondegenerate (M.exteriorDerivative (alpha q.1)) q.2) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun q : ℝ × M.Point =>
          (⟨q.2, M.liouvilleVector (alpha q.1) q.2⟩ :
            TangentBundle 𝓘(ℝ, Model d) M.Point)) V := by
  obtain ⟨U, hU, hsub, hf⟩ := halpha p.2
  let c := chartAt (Model d) p.2
  let f := fun ty : ℝ × Model d => M.formInChart p.2 (alpha ty.1) ty.2
  let B := fun ty : ℝ × Model d => extDeriv (fun z => f (ty.1, z)) ty.2
  let A := fun ty : ℝ × Model d => chartContraction (B ty)
  let b := fun ty : ℝ × Model d => (chartOneFormEquiv d).symm (f ty)
  have hB : ContDiffOn ℝ ∞ B U := contDiffOn_spatialExtDeriv f U hU hf
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model d) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A U := contDiffOn_const.clm_comp (hcur.comp_contDiffOn hB)
  have hb : ContDiffOn ℝ ∞ b U := (chartOneFormEquiv d).symm.contDiff.comp_contDiffOn hf
  have hres (ty : ℝ × Model d) (hty : ty ∈ U) (hy : ty.2 ∈ c.target) :
      M.formInChart p.2 (M.exteriorDerivative (alpha ty.1)) ty.2 = B ty := by
    have hs : ContDiffAt ℝ ∞ (fun z => f (ty.1, z)) ty.2 :=
      (hf.contDiffAt (hU.mem_nhds hty)).comp ty.2 (contDiffAt_const.prodMk contDiffAt_id)
    exact M.formInChart_exteriorDerivative_of_contDiffAt (alpha ty.1) p.2 ty.2 hy hs
  let W := (U ∩ (univ ×ˢ c.target)) ∩ A ⁻¹' {T | T.IsInvertible}
  have hW : IsOpen W := (hA.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (hU.inter (isOpen_univ.prod c.open_target))
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hactual (ty : ℝ × Model d) (hty : ty ∈ W) :
      M.Nondegenerate (M.exteriorDerivative (alpha ty.1)) (c.symm ty.2) := by
    apply M.nondegenerate_of_formInChart _ p.2 hty.1.2.2
    rw [hres ty hty.1.1 hty.1.2.2]
    exact nondegenerate_of_chartContraction_invertible (B ty) hty.2
  have hAi : ContDiffOn ℝ ∞ (fun ty => (A ty).inverse) W := by
    intro ty hty
    exact hty.2.contDiffAt_map_inverse.comp_contDiffWithinAt ty
      (hA ty hty.1.1 |>.mono (fun _ hw => hw.1.1))
  have hfield : ContDiffOn ℝ ∞ (fun ty : ℝ × Model d =>
      M.vectorInChart p.2 (M.liouvilleVector (alpha ty.1)) ty.2) W := by
    apply (hAi.clm_apply (hb.mono (fun _ hw => hw.1.1))).congr
    intro ty hty
    have he := M.liouvilleVector_chart_eq (alpha ty.1) p.2 hty.1.2.2 (hactual ty hty)
    rw [hres ty hty.1.1 hty.1.2.2] at he
    exact he
  let g := fun q : ℝ × M.Point => (q.1, c q.2)
  let V := (univ ×ˢ c.source) ∩ g ⁻¹' W
  have hg : ContinuousOn g (univ ×ˢ c.source) :=
    continuousOn_fst.prodMk (c.continuousOn.comp continuousOn_snd (fun _ hq => hq.2))
  have hV : IsOpen V := hg.isOpen_inter_preimage (isOpen_univ.prod c.open_source) hW
  have hps : p.2 ∈ c.source := mem_chart_source _ _
  have hpt : c p.2 ∈ c.target := c.map_source hps
  have hpU : (p.1, c p.2) ∈ U := hsub ⟨ht, hpt⟩
  have hpW : (p.1, c p.2) ∈ W := by
    refine ⟨⟨hpU, mem_univ _, hpt⟩, ?_⟩
    change (chartContraction (B (p.1, c p.2))).IsInvertible
    rw [← hres _ hpU hpt]
    apply chartContraction_invertible
    apply M.nondegenerate_formInChart _ p.2 hpt
    change M.Nondegenerate (M.exteriorDerivative (alpha p.1)) (c.symm (c p.2))
    simpa only [c.left_inv hps] using hnd
  refine ⟨V, hV, ⟨⟨mem_univ _, hps⟩, hpW⟩, ?_, ?_⟩
  · intro q hq
    have hn := hactual (g q) hq.2
    simpa only [g, c.left_inv hq.1.2] using hn
  · intro q hq
    exact (M.contMDiffAt_familySection_of_chart
      (fun t => M.liouvilleVector (alpha t)) p.2 q hq.1.2
      (hfield.contDiffAt (hW.mem_nhds hq.2))).contMDiffWithinAt

end SmoothManifold

namespace CompactDomain

set_option backward.isDefEq.respectTransparency false in
/-- From the actual varying primitives, construct one common open
parameter–space neighborhood containing the whole compact family. The
canonical fields satisfy the actual contraction equation there, are jointly `C∞`, and agree
with the supplied Liouville fields on the compact carrier. -/
theorem exists_liouvilleFamily_nondegenerateNeighborhood {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (halpha : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    ∃ alpha : ℝ → D.extension.Form 1,
      D.extension.IsSmoothFormFamily alpha ∧
      (∀ t : Parameter, alpha t.val = (L t).primitive) ∧
      ∃ V : TopologicalSpace.Opens (ℝ × D.extension.Point),
        parameterInterval ×ˢ D.carrier ⊆ (V : Set (ℝ × D.extension.Point)) ∧
        (∀ p ∈ V, D.extension.Nondegenerate
          (D.extension.exteriorDerivative (alpha p.1)) p.2) ∧
        (∀ p ∈ V, D.extension.LiouvilleEquation (alpha p.1) p.2
          (D.extension.liouvilleVector (alpha p.1) p.2)) ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
          (fun p : ℝ × D.extension.Point =>
            (⟨p.2, D.extension.liouvilleVector (alpha p.1) p.2⟩ :
              TangentBundle 𝓘(ℝ, Model d) D.extension.Point)) V ∧
        (∀ t : Parameter, ∀ x ∈ D.carrier,
          D.extension.liouvilleVector (alpha t.val) x = (L t).field x) := by
  obtain ⟨alpha, hs, he⟩ := halpha
  let S : Set (Set (ℝ × D.extension.Point)) := {U | IsOpen U ∧
    (∀ p ∈ U, D.extension.Nondegenerate (D.extension.exteriorDerivative (alpha p.1)) p.2) ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × D.extension.Point =>
        (⟨p.2, D.extension.liouvilleVector (alpha p.1) p.2⟩ :
          TangentBundle 𝓘(ℝ, Model d) D.extension.Point)) U}
  have hV : IsOpen (⋃₀ S) := isOpen_sUnion (fun _ hU => hU.1)
  have hnV : ∀ p ∈ ⋃₀ S, D.extension.Nondegenerate
      (D.extension.exteriorDerivative (alpha p.1)) p.2 := by
    intro p hp
    obtain ⟨U, hU, hpU⟩ := mem_sUnion.mp hp
    exact hU.2.1 p hpU
  refine ⟨alpha, hs, he, ⟨⋃₀ S, hV⟩, ?_, hnV, ?_, ?_, ?_⟩
  · intro p hp
    have hn : D.extension.Nondegenerate (D.extension.exteriorDerivative (alpha p.1)) p.2 := by
      rw [he ⟨p.1, hp.1⟩]
      exact (L ⟨p.1, hp.1⟩).symplectic.2.2 p.2 hp.2
    obtain ⟨U, hU, hpU, hnU, hzU⟩ :=
      D.extension.exists_liouvilleVector_family_neighborhood_at alpha hs p hp.1 hn
    exact mem_sUnion.mpr ⟨U, ⟨hU, hnU, hzU⟩, hpU⟩
  · intro p hp
    exact D.extension.liouvilleVector_contraction _ _
      (D.extension.liouvilleEquation_exists _ _ (hnV p hp))
  · intro p hp
    obtain ⟨U, hU, hpU⟩ := mem_sUnion.mp hp
    exact ((hU.2.2).contMDiffAt (hU.1.mem_nhds hpU)).contMDiffWithinAt
  · intro t x hx
    rw [he t]
    exact ((L t).field_eq_liouvilleVector x hx).symm

end CompactDomain
end FsFltz.Geometry
