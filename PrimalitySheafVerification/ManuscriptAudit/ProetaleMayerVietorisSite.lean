import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
import PrimalitySheafVerification.ManuscriptAudit.ProetaleTwoOpenHOne

/-! A two-open native pro-étale Mayer–Vietoris square in the universe of
the actual continuous-coefficient cohomology. -/

namespace ManuscriptAudit.ProetaleMayerVietorisSite

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleOpenLocalLifts (identityObject openObject openArrow)
open ProetaleTwoOpenHOne (twoOpenCover)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev J (X : Scheme.{0}) := Scheme.ProEt.topology X

/-- The same pro-étale site with morphisms in the native coefficient universe. -/
abbrev siteEquivalence (X : Scheme.{0}) : X.ProEt ≌ AsSmall.{1} (X.ProEt) :=
  AsSmall.equiv

abbrev topology (X : Scheme.{0}) : GrothendieckTopology (AsSmall.{1} X.ProEt) :=
  (siteEquivalence X).inverse.inducedTopology (J X)

/-- Actual native sheaves are transported along the equivalent larger-Hom site. -/
def sheafEquivalence (X : Scheme.{0}) : Sheaf (J X) A ≌ Sheaf (topology X) A :=
  (siteEquivalence X).sheafCongr (J X) (topology X) A

local instance inverse_additive (X : Scheme.{0}) :
    (sheafEquivalence X).inverse.Additive :=
  (sheafEquivalence X).inverse.additive_of_preserves_binary_products

variable {U V W X : Scheme.{0}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  (a : openObject l ⟶ openObject j) (b : openObject l ⟶ openObject k)
  (hD : IsPullback a b (openArrow j) (openArrow k))
  (hCover : Set.range j ∪ Set.range k = Set.univ)

private abbrev F := (siteEquivalence X).functor

include hCover in
private theorem twoArrows_cover :
    Sieve.ofTwoArrows ((F (X := X)).map (openArrow j)) ((F (X := X)).map (openArrow k)) ∈
      topology X ((F (X := X)).obj (identityObject X)) := by
  apply (Functor.mem_inducedTopology_iff_of_isCoverDense
    (G := (siteEquivalence X).inverse) (K := J X) _).mpr
  rw [Sieve.functorPushforward_ofArrows]
  refine (J X).superset_covering ?_ (twoOpenCover j k hCover)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  cases i
  · exact Sieve.ofArrows_mk _ _ WalkingPair.left
  · exact Sieve.ofArrows_mk _ _ WalkingPair.right

include hD hCover in
/-- The higher-universe presentation of the actual native open cover and pullback. -/
def openCoverSquare : (topology X).MayerVietorisSquare := by
  let f := F (X := X)
  let sq : Square (AsSmall.{1} X.ProEt) :=
    { f₁₂ := f.map a
      f₁₃ := f.map b
      f₂₄ := f.map (openArrow j)
      f₃₄ := f.map (openArrow k)
      fac := by rw [← f.map_comp, ← f.map_comp, hD.w] }
  letI : Mono sq.f₂₄ := inferInstanceAs (Mono (f.map (openArrow j)))
  letI : Mono sq.f₃₄ := inferInstanceAs (Mono (f.map (openArrow k)))
  have hP : sq.IsPullback :=
    IsPullback.of_isLimit (isLimitPullbackConeMapOfIsLimit f hD.w hD.isLimit)
  exact GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := topology X) sq hP (twoArrows_cover j k hCover)

/-- The genuine exact Mayer–Vietoris complex transported back to native pro-étale sheaves. -/
def coverComplex : ShortComplex (Sheaf (J X) A) :=
  (openCoverSquare j k l a b hD hCover).shortComplex.map (sheafEquivalence X).inverse

theorem coverComplex_shortExact : (coverComplex j k l a b hD hCover).ShortExact :=
  (openCoverSquare j k l a b hD hCover).shortComplex_shortExact.map_of_exact
    (sheafEquivalence X).inverse

end
end ManuscriptAudit.ProetaleMayerVietorisSite

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleMayerVietorisSite.sheafEquivalence,
      ``ManuscriptAudit.ProetaleMayerVietorisSite.openCoverSquare,
      ``ManuscriptAudit.ProetaleMayerVietorisSite.coverComplex_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
