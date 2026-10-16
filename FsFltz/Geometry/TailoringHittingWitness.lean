import FsFltz.Geometry.TailoringHittingWitnessExtension
import FsFltz.Geometry.SmoothEmbeddingFactorization
import FsFltz.Geometry.TailoringMarkedOuterBoundary
import FsFltz.Geometry.IntrinsicBoundaryWitnessFamily

/-!
# Positive witnesses on the actual marked outer boundary

Source: `geometric-part-fsf-proof.tex`, `eq:hittingprimitive` and
`eq:ribbonprimitive`, lines 1818–1875. The actual full-ribbon hitting
embeddings factor through the retained native outer boundary. The compact
parameter/ribbon graph constructs a globally positive jointly smooth
boundary witness with the exact required exponential restriction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz
open Geometry Geometry.SmoothManifold

variable {n : ℕ}
local instance hittingWitnessCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance hittingWitnessSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- The actual compact hitting graph constructs smooth boundary embeddings
and a jointly smooth positive witness on the whole native boundary, preserving
its prescribed value on every point of the same full compact ribbon. -/
theorem exists_native_boundary_hitting_witness
    {d b : ℕ} (F : CompactDomain d) (B : SmoothManifold b)
    (i : B.SmoothEmbedding (lgManifold n))
    (V : TopologicalSpace.Opens ℝ) {P : Set ℝ} (hP : IsCompact P) (hPV : P ⊆ V)
    (e : V → F.extension.SmoothEmbedding (lgManifold n))
    (hit : ℝ × F.extension.Point → LGSpace n)
    (he : ∀ k x, (e k).map x = hit (k.val, x))
    (hhit : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, Model (2 * n)) ∞ hit ((V : Set ℝ) ×ˢ univ))
    (hrange : ∀ k x, (e k).map x ∈ range i.map)
    (τ : ℝ × F.extension.Point → ℝ)
    (hτ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, ℝ) ∞ τ ((V : Set ℝ) ×ˢ univ)) :
    ∃ j : V → F.extension.SmoothEmbedding B,
      (∀ k x, i.map ((j k).map x) = (e k).map x) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model b) ∞
        (fun p : V × F.extension.Point => (j p.1).map p.2) ∧
      ∃ w : ℝ × B.Point → ℝ,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model b)) 𝓘(ℝ, ℝ) ∞ w ∧
        (∀ p, 0 < w p) ∧
        ∀ k (hk : k ∈ P), ∀ x ∈ F.carrier,
          w (k, (j ⟨k, hPV hk⟩).map x) = Real.exp (-τ (k, x)) := by
  have hlift (k : V) := exists_smoothEmbedding_factor B F.extension (lgManifold n) i (e k)
    (by rintro _ ⟨x, rfl⟩; exact hrange k x)
  choose j hj using hlift
  let q : V × F.extension.Point → B.Point := fun p => (j p.1).map p.2
  have hpre : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun p : V × F.extension.Point => (p.1.val, p.2)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  have hcomp : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, Model (2 * n)) ∞ (i.map ∘ q) := by
    have heq : i.map ∘ q = fun p : V × F.extension.Point => hit (p.1.val, p.2) := by
      funext p
      exact (hj p.1 p.2).trans (he p.1 p.2)
    rw [heq]
    intro p
    exact (hhit.contMDiffAt ((V.isOpen.prod isOpen_univ).mem_nhds
      ⟨p.1.property, mem_univ _⟩)).comp p (hpre p)
  let : ChartedSpace (ℝ × Model d) (V × F.extension.Point) :=
    prodChartedSpace ℝ V (Model d) F.extension.Point
  have hq : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, Model b) ∞ q := by
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := Model d)] at hcomp ⊢
    exact contMDiff_of_comp_embedding i.map.contMDiff i.embedding i.immersion hcomp
  let Γ : ℝ × F.extension.Point → ℝ × LGSpace n := fun p => (p.1, hit p)
  have hΓ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ Γ ((V : Set ℝ) ×ˢ univ) :=
    contMDiff_fst.contMDiffOn.prodMk hhit
  have hΓinj : InjOn Γ (P ×ˢ F.carrier) := by
    rintro ⟨k, x⟩ ⟨hk, hx⟩ ⟨l, y⟩ ⟨hl, hy⟩ hxy
    have hkl : k = l := congrArg Prod.fst hxy
    subst l
    refine Prod.ext rfl ((e ⟨k, hPV hk⟩).embedding.injective ?_)
    simpa only [he] using congrArg Prod.snd hxy
  have hΓimm (p : ℝ × F.extension.Point) (hp : p ∈ P ×ˢ F.carrier) :
      Function.Injective (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) Γ p) := by
    have hd := (hhit.contMDiffAt ((V.isOpen.prod isOpen_univ).mem_nhds
      ⟨hPV hp.1, mem_univ _⟩)).mdifferentiableAt (by simp)
    apply (F.extension.injective_mfderiv_parameterGraph_iff (lgManifold n)
      (j := fun k x => hit (k, x)) hd).mpr
    have heq : (fun x => hit (p.1, x)) = (e ⟨p.1, hPV hp.1⟩).map :=
      funext (fun x => (he ⟨p.1, hPV hp.1⟩ x).symm)
    rw [heq]
    exact (e ⟨p.1, hPV hp.1⟩).immersion p.2
  have hsource : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (ℝ × F.extension.Point) := inferInstance
  have htarget : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (ℝ × LGSpace n) := inferInstance
  let : ChartedSpace (ℝ × Model d) (ℝ × F.extension.Point) :=
    prodChartedSpace ℝ ℝ (Model d) F.extension.Point
  let : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × F.extension.Point) := by
    rw [← modelWithCornersSelf_prod] at hsource
    exact hsource
  let : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
    prodChartedSpace ℝ ℝ (Model (2 * n)) (LGSpace n)
  let : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
    rw [← modelWithCornersSelf_prod] at htarget
    exact htarget
  have hΓ' : ContMDiffOn 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model (2 * n)) ∞ Γ
      ((V : Set ℝ) ×ˢ univ) := by
    simpa only [← modelWithCornersSelf_prod] using hΓ
  have hΓimm' : ∀ p ∈ P ×ˢ F.carrier, Function.Injective
      (mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model (2 * n)) Γ p) := by
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := Model d),
      ← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := Model (2 * n))] at hΓimm
    exact hΓimm
  have hτ' : ContMDiffOn 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ∞
      (fun p => -τ p) ((V : Set ℝ) ×ˢ univ) := by
    simpa only [← modelWithCornersSelf_prod] using hτ.neg
  obtain ⟨a, ha, haeq⟩ := exists_scalarExtension_of_compact_injective_immersion
    (hP.prod F.compact) (V.isOpen.prod isOpen_univ)
    (prod_mono hPV (subset_univ _)) hΓ' hΓinj hΓimm' hτ'
  let w : ℝ × B.Point → ℝ := fun p => Real.exp (a (p.1, i.map p.2))
  have haw : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℝ) ∞ a := by
    simpa only [← modelWithCornersSelf_prod] using ha
  have hw : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model b)) 𝓘(ℝ, ℝ) ∞ w :=
    Real.contDiff_exp.contMDiff.comp
      (haw.comp (contMDiff_fst.prodMk (i.map.contMDiff.comp contMDiff_snd)))
  refine ⟨j, hj, hq, w, hw, fun p => Real.exp_pos _, ?_⟩
  intro k hk x hx
  change Real.exp (a (k, i.map ((j ⟨k, hPV hk⟩).map x))) = _
  rw [hj, he]
  exact congrArg Real.exp (haeq (k, x) ⟨hk, hx⟩)

end FsFltz
