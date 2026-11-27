import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenKernelHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedPairSupport
import PrimalitySheafVerification.ManuscriptAudit.SheafProductSectionExt

/-! Native continuous sections over an open lift arbitrary restrictions
to one rational point, and to a pair if one point is outside the open. -/

namespace ManuscriptAudit.ProetaleAdicPointOpenSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleAdicClosedPairSupport (boundary pairRestriction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} (L : Type) [Field L]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev M := ℤ_[ℓ]

theorem diagonal_surjective (i : Spec (CommRingCat.of L) ⟶ X) (T : X.ProEt)
    [IsOpenImmersion T.hom] :
    Function.Surjective ((diagonal (M ℓ) i).hom.app (op T)) := by
  classical
  let V := pullback T.hom i
  have hs : Subsingleton V := (pullback.snd T.hom i).isOpenEmbedding.injective.subsingleton
  intro s
  let f : C(V, M ℓ) := s.down
  let c : M ℓ := if h : Nonempty V then f (Classical.choice h) else 0
  refine ⟨⟨ContinuousMap.const T.left c⟩, ?_⟩
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change c = f x
  dsimp only [c]
  rw [dif_pos ⟨x⟩]
  exact congrArg f (hs.elim _ _)

private theorem eq_off_support (i : Spec (CommRingCat.of L) ⟶ X) (T : X.ProEt)
    (h : Disjoint (Set.range T.hom) (Set.range i))
    (a b : (functionsOver (M ℓ) i).obj.obj (op T)) : a = b := by
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change ↥(pullback T.hom i : Scheme.{0}) at x
  have hx : T.hom (pullback.fst T.hom i x) = i (pullback.snd T.hom i x) :=
    congrArg (fun f : pullback T.hom i ⟶ X ↦ f x) (pullback.condition (f := T.hom) (g := i))
  exact (Set.disjoint_left.mp h ⟨_, rfl⟩ ⟨_, hx.symm⟩).elim

variable (i₀ i₁ : Spec (CommRingCat.of L) ⟶ X) (T : X.ProEt) [IsOpenImmersion T.hom]

theorem pair_surjective_off_second (h : Disjoint (Set.range T.hom) (Set.range i₁)) :
    Function.Surjective ((pairRestriction i₀ i₁ ℓ).hom.app (op T)) := by
  let p : boundary i₀ i₁ ℓ ⟶ functionsOver (M ℓ) i₀ := prod.fst
  intro s
  obtain ⟨f, hf⟩ := diagonal_surjective L ℓ i₀ T (p.hom.app (op T) s)
  refine ⟨f, ?_⟩
  apply SheafProductSectionExt.section_ext
  · change ((pairRestriction i₀ i₁ ℓ ≫ p).hom.app (op T)) f = p.hom.app (op T) s
    rw [show pairRestriction i₀ i₁ ℓ ≫ p = diagonal (M ℓ) i₀ from prod.lift_fst _ _]
    exact hf
  · exact eq_off_support L ℓ i₁ T h _ _

theorem pair_surjective_off_first (h : Disjoint (Set.range T.hom) (Set.range i₀)) :
    Function.Surjective ((pairRestriction i₀ i₁ ℓ).hom.app (op T)) := by
  let p : boundary i₀ i₁ ℓ ⟶ functionsOver (M ℓ) i₁ := prod.snd
  intro s
  obtain ⟨f, hf⟩ := diagonal_surjective L ℓ i₁ T (p.hom.app (op T) s)
  refine ⟨f, ?_⟩
  apply SheafProductSectionExt.section_ext
  · exact eq_off_support L ℓ i₀ T h _ _
  · change ((pairRestriction i₀ i₁ ℓ ≫ p).hom.app (op T)) f = p.hom.app (op T) s
    rw [show pairRestriction i₀ i₁ ℓ ≫ p = diagonal (M ℓ) i₁ from prod.lift_snd _ _]
    exact hf

end

end ManuscriptAudit.ProetaleAdicPointOpenSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicPointOpenSections.diagonal_surjective,
      ``ManuscriptAudit.ProetaleAdicPointOpenSections.pair_surjective_off_second,
      ``ManuscriptAudit.ProetaleAdicPointOpenSections.pair_surjective_off_first] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
