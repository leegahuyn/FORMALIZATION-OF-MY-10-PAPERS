import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietoris
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleFreeRepresentable

/-! The actual small-étale Mayer–Vietoris sequence in the coefficient universe of change of sites. -/

namespace ManuscriptAudit.EtaleMayerVietorisHigh

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EtaleTwoOpenHOne (openArrow identityObject)
open EtaleProetaleFreeRepresentable (raisedEtale etaleTopology etaleSheafEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U V W X : Scheme.{0}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  (a : Scheme.Etale.mk l ⟶ Scheme.Etale.mk j)
  (b : Scheme.Etale.mk l ⟶ Scheme.Etale.mk k)
  (hD : IsPullback a b (openArrow j) (openArrow k))
  (hCover : Set.range j ∪ Set.range k = Set.univ)

private abbrev F := (raisedEtale X).functor

private theorem openArrow_mono {Y X : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] :
    Mono (openArrow f) where
  right_cancellation g h e := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono f).mp
    exact congrArg (fun t => t.left) e

include hCover in
private theorem twoArrows_cover :
    Sieve.ofTwoArrows ((F (X := X)).map (openArrow j)) ((F (X := X)).map (openArrow k)) ∈
      etaleTopology X ((F (X := X)).obj (identityObject X)) := by
  have h₀ : Sieve.ofTwoArrows (openArrow j) (openArrow k) ∈ X.smallEtaleTopology (identityObject X) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ Set.range j ∪ Set.range k := hCover.symm ▸ Set.mem_univ x
    rcases hx with hj | hk
    · exact Set.mem_iUnion.2 ⟨WalkingPair.left, hj⟩
    · exact Set.mem_iUnion.2 ⟨WalkingPair.right, hk⟩
  apply (Functor.mem_inducedTopology_iff_of_isCoverDense
    (G := (raisedEtale X).inverse) (K := X.smallEtaleTopology) _).mpr
  rw [Sieve.functorPushforward_ofArrows]
  refine X.smallEtaleTopology.superset_covering ?_ h₀
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  cases i
  · exact Sieve.ofArrows_mk _ _ WalkingPair.left
  · exact Sieve.ofArrows_mk _ _ WalkingPair.right

include hD hCover in
def highSquare : (etaleTopology X).MayerVietorisSquare := by
  let f := F (X := X)
  let sq : Square (AsSmall.{1} X.Etale) :=
    { f₁₂ := f.map a
      f₁₃ := f.map b
      f₂₄ := f.map (openArrow j)
      f₃₄ := f.map (openArrow k)
      fac := by rw [← f.map_comp, ← f.map_comp, hD.w] }
  letI : Mono (openArrow j) := openArrow_mono j
  letI : Mono (openArrow k) := openArrow_mono k
  letI : Mono sq.f₂₄ := inferInstanceAs (Mono (f.map (openArrow j)))
  letI : Mono sq.f₃₄ := inferInstanceAs (Mono (f.map (openArrow k)))
  have hP : sq.IsPullback :=
    IsPullback.of_isLimit (isLimitPullbackConeMapOfIsLimit f hD.w hD.isLimit)
  exact GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := etaleTopology X) sq hP (twoArrows_cover j k hCover)

def coverComplex : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{1}) :=
  (highSquare j k l a b hD hCover).shortComplex.map (etaleSheafEquiv X).inverse

theorem coverComplex_shortExact : (coverComplex j k l a b hD hCover).ShortExact := by
  let E := (etaleSheafEquiv X).inverse
  letI : E.Additive := E.additive_of_preserves_binary_products
  exact (highSquare j k l a b hD hCover).shortComplex_shortExact.map_of_exact E

end
end ManuscriptAudit.EtaleMayerVietorisHigh

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleMayerVietorisHigh.coverComplex_shortExact
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
