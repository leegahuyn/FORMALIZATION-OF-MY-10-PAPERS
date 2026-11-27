import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GaloisOverlapEtale
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleDisjointSections

/-!
# Sections on the Galois overlaps

Sections over the double overlap are the product of sections over
its disjoint Galois components. On the triple overlap, restriction
to the Galois components detects equality.
-/

namespace ManuscriptAudit.GaloisTensorSquare

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (F L : Type) [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

private abbrev X := Spec (CommRingCat.of F)
private abbrev U := Spec (CommRingCat.of L)

private theorem component_disjoint (σ τ : L ≃ₐ[F] L) (h : σ ≠ τ) :
    Disjoint (Set.range (component F L σ)) (Set.range (component F L τ)) := by
  let e := sigmaIsoPullback F L
  let s := AlgebraicGeometry.sigmaMk (fun _ : L ≃ₐ[F] L ↦ U L)
  have hs (g : L ≃ₐ[F] L) (y : U L) : e.hom (s ⟨g, y⟩) = component F L g y := by
    change (sigmaIsoPullback F L).hom (AlgebraicGeometry.sigmaMk _ ⟨g, y⟩) = _
    rw [AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply, sigmaIsoPullback_ι]
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  have he : e.hom (s ⟨σ, a⟩) = e.hom (s ⟨τ, b⟩) :=
    (hs σ a).trans (hb.symm.trans (hs τ b).symm)
  have hi : Function.Injective e.hom := (Scheme.homeoOfIso e).injective
  exact h (congrArg Sigma.fst (s.injective (hi he)))

variable (M : Sheaf (X F).smallEtaleTopology AddCommGrpCat.{0})

/-- Actual Galois components identify double-overlap sections with
all families of sections over the cover object. -/
def pairSectionsEquiv :
    (M.obj.obj (op (pairObject F L))) ≃+
      ((L ≃ₐ[F] L) → M.obj.obj (op (fieldObject F L))) :=
  SmallEtaleDisjointSections.sectionsEquivOfDisjointCover M (pairComponentArrow F L)
    (component_jointly_surjective F L)
    (fun σ ↦ by
      letI := component_isOpenImmersion F L σ
      change Mono (component F L σ)
      infer_instance)
    (component_disjoint F L)

@[simp] theorem pairSectionsEquiv_apply
    (a : M.obj.obj (op (pairObject F L))) (σ : L ≃ₐ[F] L) :
    pairSectionsEquiv F L M a σ = M.obj.map (pairComponentArrow F L σ).op a := rfl

/-- Two sections on the actual triple overlap are equal if they
have the same restriction to every Galois component. -/
theorem tripleSections_ext (a b : M.obj.obj (op (tripleObject F L)))
    (h : ∀ σ τ : L ≃ₐ[F] L,
      M.obj.map (tripleComponentArrow F L σ τ).op a =
        M.obj.map (tripleComponentArrow F L σ τ).op b) : a = b := by
  let g (i : (L ≃ₐ[F] L) × (L ≃ₐ[F] L)) := tripleComponentArrow F L i.1 i.2
  have hCov (x : (tripleObject F L).left) :
      ∃ (i : (L ≃ₐ[F] L) × (L ≃ₐ[F] L)) (y : U L), (g i).left y = x := by
    obtain ⟨σ, τ, y, hy⟩ := tripleComponent_jointly_surjective F L x
    exact ⟨(σ, τ), y, hy⟩
  apply SmallEtaleDisjointSections.restriction_injective M g hCov
  funext i
  exact h i.1 i.2

end

end ManuscriptAudit.GaloisTensorSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisTensorSquare.pairSectionsEquiv,
      ``ManuscriptAudit.GaloisTensorSquare.pairSectionsEquiv_apply,
      ``ManuscriptAudit.GaloisTensorSquare.tripleSections_ext] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
