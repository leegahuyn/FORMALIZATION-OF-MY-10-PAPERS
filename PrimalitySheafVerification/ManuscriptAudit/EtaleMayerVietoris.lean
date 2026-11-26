import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne

/-!
# The actual small étale Mayer–Vietoris square of two opens

The displayed open objects form a pullback square at their common
overlap and cover the terminal object. Mathlib's native
Mayer–Vietoris sequence gives restriction, restriction difference,
and connecting arrows for each consecutive pair of degrees.
-/

namespace ManuscriptAudit.EtaleMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleTwoOpenHOne

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U V W X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
variable (a : Scheme.Etale.mk l ⟶ Scheme.Etale.mk j)
variable (b : Scheme.Etale.mk l ⟶ Scheme.Etale.mk k)
variable (hD : IsPullback a b (openArrow j) (openArrow k))
variable (hCover : Set.range j ∪ Set.range k = Set.univ)

private theorem openArrow_isMono {B X : Scheme.{u}} (f : B ⟶ X) [IsOpenImmersion f] :
    Mono (openArrow f) where
  right_cancellation g h e := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono f).mp
    exact congrArg (fun g => g.left) e

private theorem twoArrows_cover :
    Sieve.ofTwoArrows (openArrow j) (openArrow k) ∈ X.smallEtaleTopology (identityObject X) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ Set.range j ∪ Set.range k := hCover.symm ▸ Set.mem_univ x
  rcases hx with hj | hk
  · exact Set.mem_iUnion.2 ⟨WalkingPair.left, hj⟩
  · exact Set.mem_iUnion.2 ⟨WalkingPair.right, hk⟩

/-- The native Mayer–Vietoris square of a two-open cover on the small étale site. -/
def openCoverSquare : X.smallEtaleTopology.MayerVietorisSquare := by
  let sq : Square X.Etale :=
    { f₁₂ := a, f₁₃ := b, f₂₄ := openArrow j, f₃₄ := openArrow k, fac := hD.w }
  letI : Mono sq.f₂₄ := openArrow_isMono j
  letI : Mono sq.f₃₄ := openArrow_isMono k
  exact GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback sq hD (twoArrows_cover j k hCover)

variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)

/-- The exact six-term native segment for consecutive étale cohomological degrees. -/
def openCoverSequence : ComposableArrows AddCommGrpCat.{u} 5 :=
  (openCoverSquare j k l a b hD hCover).sequence F n (n + 1) rfl

theorem openCoverSequence_exact : (openCoverSequence j k l a b hD hCover F n).Exact :=
  (openCoverSquare j k l a b hD hCover).sequence_exact F n (n + 1) rfl

end

end ManuscriptAudit.EtaleMayerVietoris

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleMayerVietoris.openCoverSquare,
      ``ManuscriptAudit.EtaleMayerVietoris.openCoverSequence_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
