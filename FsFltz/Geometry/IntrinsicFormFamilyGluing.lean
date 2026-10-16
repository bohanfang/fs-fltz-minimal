import FsFltz.Geometry.Family
import FsFltz.Geometry.SmoothForms
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Joint gluing of actual spatial form families

The jointly smooth forms in `geoemtric-part-fsf.tex`, `def:chain`, lines
163–169, extend across parameter endpoints. The foundations handoff
`sec:lean`, lines 788–814, requires this regularity on fixed presentations.
Here local germs on a closed subset of time times a boundaryless manifold
are glued by a partition of unity on that product. The sum takes place in
the actual spatial form fibers; no global smooth tangent frame is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter Function

namespace FsFltz.Geometry
namespace SmoothManifold

/-- Jointly smooth covectors and linear tangent maps have a jointly smooth
actual one-form composition. This is useful for source germ construction. -/
theorem contDiffAt_oneForm_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : G → F [⋀^Fin 1]→L[ℝ] ℝ) (B : G → E →L[ℝ] F) (z : G)
    (ha : ContDiffAt ℝ ∞ a z) (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun y => (a y).compContinuousLinearMap (B y)) z := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have h := (eF.symm.contDiff.contDiffAt.comp z ha).clm_comp hB
  have hs := eE.contDiff.contDiffAt.comp z h
  convert hs using 1
  ext y vs
  change a y (fun i => B y (vs i)) = a y (fun _ => B y (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- Joint chartwise smoothness on an actual open subset of parameter times
space. Only spatial tangent arguments enter the form. -/
def IsSmoothFormFamilyOn {d k : ℕ} (N : SmoothManifold d)
    (lam : ℝ → N.Form k) (U : Set (ℝ × N.Point)) : Prop :=
  ∀ a, ContDiffOn ℝ ∞ (fun ty => N.formInChart a (lam ty.1) ty.2)
    ((univ ×ˢ (chartAt (Model d) a).target) ∩
      (fun ty : ℝ × Model d => (ty.1, (chartAt (Model d) a).symm ty.2)) ⁻¹' U)

/-- The inverse product chart is continuous on its genuine chart domain. -/
theorem continuousOn_inverseProductChart {d : ℕ} (N : SmoothManifold d)
    (a : N.Point) : ContinuousOn
      (fun ty : ℝ × Model d => (ty.1, (chartAt (Model d) a).symm ty.2))
      (univ ×ˢ (chartAt (Model d) a).target) := by
  exact continuousOn_fst.prodMk
    ((chartAt (Model d) a).continuousOn_symm.comp continuousOn_snd
      (fun _ hy => hy.2))

/-- The chart domain corresponding to an open time-space patch is open. -/
theorem isOpen_inverseProductChart_preimage {d : ℕ} (N : SmoothManifold d)
    (a : N.Point) {U : Set (ℝ × N.Point)} (hU : IsOpen U) :
    IsOpen ((univ ×ˢ (chartAt (Model d) a).target) ∩
      (fun ty : ℝ × Model d => (ty.1, (chartAt (Model d) a).symm ty.2)) ⁻¹' U) := by
  exact (N.continuousOn_inverseProductChart a).isOpen_inter_preimage
    (isOpen_univ.prod (chartAt (Model d) a).open_target) hU

theorem isSmoothFormFamilyOn_zero {d k : ℕ} (N : SmoothManifold d)
    (U : Set (ℝ × N.Point)) :
    N.IsSmoothFormFamilyOn (fun _ => (0 : N.Form k)) U := by
  intro a
  simpa only [formInChart_zero, Pi.zero_apply] using
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ × Model d =>
      (0 : Model d [⋀^Fin k]→L[ℝ] ℝ)) _)

/-- All-real joint smoothness implies the existing family predicate with
smooth extension across the closed parameter interval. -/
theorem IsSmoothFormFamilyOn.isSmoothFormFamily {d k : ℕ}
    {N : SmoothManifold d} {lam : ℝ → N.Form k}
    (hlam : N.IsSmoothFormFamilyOn lam univ) : N.IsSmoothFormFamily lam := by
  intro a
  refine ⟨univ ×ˢ (chartAt (Model d) a).target,
    isOpen_univ.prod (chartAt (Model d) a).open_target,
    Set.prod_mono (subset_univ _) Subset.rfl, ?_⟩
  simpa only [preimage_univ, inter_univ] using hlam a

private theorem contDiffOn_scalar_inverseProductChart {d : ℕ}
    (N : SmoothManifold d) (a : N.Point) {w : ℝ × N.Point → ℝ}
    (hw : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞ w) :
    ContDiffOn ℝ ∞
      (fun ty : ℝ × Model d => w (ty.1, (chartAt (Model d) a).symm ty.2))
      (univ ×ˢ (chartAt (Model d) a).target) := by
  have hinv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun ty : ℝ × Model d => (ty.1, (chartAt (Model d) a).symm ty.2))
      (univ ×ˢ (chartAt (Model d) a).target) :=
    contMDiff_fst.contMDiffOn.prodMk
      (contMDiffOn_chart_symm.comp contMDiff_snd.contMDiffOn (fun _ hy => hy.2))
  rw [← modelWithCornersSelf_prod] at hw hinv
  rw [chartedSpaceSelf_prod] at hinv
  exact contMDiffOn_iff_contDiffOn.mp (hw.comp_contMDiffOn hinv)

/-- Partition weights multiply actual form fibers at the same time-space
point. The pointwise finite support makes this a finite sum in each fiber. -/
def partitionFormFamily {d k : ℕ} (N : SmoothManifold d) {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (ℝ × N.Point) univ) (g : ι → ℝ → N.Form k) : ℝ → N.Form k :=
  fun t x => ∑ i ∈ ρ.finsupport (t, x), ρ i (t, x) • g i t x

private theorem formInChart_partitionFormFamily {d k : ℕ}
    (N : SmoothManifold d) {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (ℝ × N.Point) univ) (g : ι → ℝ → N.Form k)
    (a : N.Point) (ty : ℝ × Model d) :
    N.formInChart a (N.partitionFormFamily ρ g ty.1) ty.2 =
      ∑ i ∈ ρ.finsupport (ty.1, (chartAt (Model d) a).symm ty.2),
        ρ i (ty.1, (chartAt (Model d) a).symm ty.2) •
          N.formInChart a (g i ty.1) ty.2 := by
  classical
  ext v
  simp only [formInChart, partitionFormFamily,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]

/-- A subordinate smooth partition glues local jointly smooth actual forms.
Local finiteness reduces the chart coefficient sum near each point to one
fixed finite sum, without choosing a global tangent trivialization. -/
theorem isSmoothFormFamilyOn_partitionFormFamily {d k : ℕ}
    (N : SmoothManifold d) {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (ℝ × N.Point) univ) (g : ι → ℝ → N.Form k) (U : ι → Set (ℝ × N.Point))
    (hρ : ρ.IsSubordinate U) (hU : ∀ i, IsOpen (U i))
    (hg : ∀ i, N.IsSmoothFormFamilyOn (g i) (U i)) :
    N.IsSmoothFormFamilyOn (N.partitionFormFamily ρ g) univ := by
  classical
  intro a ty hty
  have htarget : ty ∈ univ ×ˢ (chartAt (Model d) a).target := hty.1
  let Q : ℝ × Model d → ℝ × N.Point :=
    fun z => (z.1, (chartAt (Model d) a).symm z.2)
  let s := ρ.fintsupport (Q ty)
  have hQ : ContinuousAt Q ty :=
    (N.continuousOn_inverseProductChart a).continuousAt
      ((isOpen_univ.prod (chartAt (Model d) a).open_target).mem_nhds htarget)
  have hsum : ContDiffAt ℝ ∞
      (fun z : ℝ × Model d => ∑ i ∈ s, ρ i (Q z) •
        N.formInChart a (g i z.1) z.2) ty := by
    apply ContDiffAt.sum
    intro i hi
    have hQi : Q ty ∈ U i := hρ i ((ρ.mem_fintsupport_iff (Q ty) i).mp hi)
    have hlocal : ContDiffAt ℝ ∞
        (fun z : ℝ × Model d => N.formInChart a (g i z.1) z.2) ty :=
      (hg i a).contDiffAt
        ((N.isOpen_inverseProductChart_preimage a (hU i)).mem_nhds ⟨htarget, hQi⟩)
    exact ((N.contDiffOn_scalar_inverseProductChart a (ρ i).contMDiff).contDiffAt
      ((isOpen_univ.prod (chartAt (Model d) a).open_target).mem_nhds htarget)).smul hlocal
  apply (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hQ (ρ.eventually_finsupport_subset (Q ty))] with z hz
  rw [N.formInChart_partitionFormFamily]
  apply Finset.sum_subset hz
  intro i _ hi
  have hw : ρ i (Q z) = 0 := by
    simpa only [ρ.mem_finsupport, mem_support, not_not] using hi
  rw [hw, zero_smul]

/-- On the prescribed carrier, matching germs give literal equality of
actual tensors, by the partition identity. -/
theorem partitionFormFamily_eq {d k : ℕ} (N : SmoothManifold d) {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (ℝ × N.Point) univ) (g : ι → ℝ → N.Form k)
    (U : ι → Set (ℝ × N.Point)) (hρ : ρ.IsSubordinate U)
    {A : Set (ℝ × N.Point)}
    {f : (p : ℝ × N.Point) → N.Tangent p.2 [⋀^Fin k]→L[ℝ] ℝ}
    (heq : ∀ i p, p ∈ U i ∩ A → g i p.1 p.2 = f p)
    {p : ℝ × N.Point} (hp : p ∈ A) : N.partitionFormFamily ρ g p.1 p.2 = f p := by
  classical
  change (∑ i ∈ ρ.finsupport p, ρ i p • g i p.1 p.2) = f p
  calc
    (∑ i ∈ ρ.finsupport p, ρ i p • g i p.1 p.2) =
        ∑ i ∈ ρ.finsupport p, ρ i p • f p := by
      apply Finset.sum_congr rfl
      intro i hi
      have hs : p ∈ support (ρ i) := by simpa only [ρ.mem_finsupport, mem_support] using hi
      rw [heq i p ⟨hρ i (subset_closure hs), hp⟩]
    _ = (∑ i ∈ ρ.finsupport p, ρ i p) • f p := Finset.sum_smul.symm
    _ = f p := by rw [ρ.sum_finsupport p (mem_univ p), one_smul]

/-- Local jointly smooth actual spatial form germs along a closed carrier
produce a global all-real jointly smooth family with precisely the prescribed
tensor values. Germs need only agree on the carrier, and can disagree away
from it. The result makes no assertion about symplecticity off an interval. -/
theorem exists_smoothFormFamilyOn_extension_of_closed {d k : ℕ}
    (N : SmoothManifold d) {A : Set (ℝ × N.Point)} (hA : IsClosed A)
    {f : (p : ℝ × N.Point) → N.Tangent p.2 [⋀^Fin k]→L[ℝ] ℝ}
    (hlocal : ∀ p ∈ A, ∃ U : Set (ℝ × N.Point),
      IsOpen U ∧ p ∈ U ∧ ∃ g : ℝ → N.Form k,
        N.IsSmoothFormFamilyOn g U ∧ ∀ q ∈ U ∩ A, g q.1 q.2 = f q) :
    ∃ lam : ℝ → N.Form k, N.IsSmoothFormFamilyOn lam univ ∧
      ∀ p ∈ A, lam p.1 p.2 = f p := by
  classical
  let : LocallyCompactSpace (ModelProd ℝ (Model d)) :=
    ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)).locallyCompactSpace
  let : LocallyCompactSpace (ℝ × N.Point) :=
    ChartedSpace.locallyCompactSpace (ModelProd ℝ (Model d)) (ℝ × N.Point)
  let : SigmaCompactSpace (ℝ × N.Point) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hloc : ∀ p : ℝ × N.Point, ∃ U : Set (ℝ × N.Point),
      IsOpen U ∧ p ∈ U ∧ ∃ g : ℝ → N.Form k,
        N.IsSmoothFormFamilyOn g U ∧ ∀ q ∈ U ∩ A, g q.1 q.2 = f q := by
    intro p
    by_cases hp : p ∈ A
    · exact hlocal p hp
    · refine ⟨Aᶜ, hA.isOpen_compl, hp, fun _ => 0,
        N.isSmoothFormFamilyOn_zero Aᶜ, ?_⟩
      intro q hq
      exact (hq.1 hq.2).elim
  choose U hU hpU g hg heq using hloc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) isClosed_univ U hU
    (fun p _ => mem_iUnion.mpr ⟨p, hpU p⟩)
  exact ⟨N.partitionFormFamily ρ g,
    N.isSmoothFormFamilyOn_partitionFormFamily ρ g U hρ hU hg,
    fun p hp => N.partitionFormFamily_eq ρ g U hρ heq hp⟩

/-- The same gluing theorem in the project's interval-family interface.
The produced family actually has joint smoothness for all real times. -/
theorem exists_smoothFormFamily_extension_of_closed {d k : ℕ}
    (N : SmoothManifold d) {A : Set (ℝ × N.Point)} (hA : IsClosed A)
    {f : (p : ℝ × N.Point) → N.Tangent p.2 [⋀^Fin k]→L[ℝ] ℝ}
    (hlocal : ∀ p ∈ A, ∃ U : Set (ℝ × N.Point),
      IsOpen U ∧ p ∈ U ∧ ∃ g : ℝ → N.Form k,
        N.IsSmoothFormFamilyOn g U ∧ ∀ q ∈ U ∩ A, g q.1 q.2 = f q) :
    ∃ lam : ℝ → N.Form k, N.IsSmoothFormFamily lam ∧
      ∀ p ∈ A, lam p.1 p.2 = f p := by
  obtain ⟨lam, hlam, heq⟩ := N.exists_smoothFormFamilyOn_extension_of_closed hA hlocal
  exact ⟨lam, hlam.isSmoothFormFamily, heq⟩

end SmoothManifold
end FsFltz.Geometry
