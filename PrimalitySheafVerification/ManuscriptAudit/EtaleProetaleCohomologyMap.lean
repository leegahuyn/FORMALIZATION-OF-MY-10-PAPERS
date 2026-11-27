import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteConstant

/-! The actual change-of-site morphisms on cohomology, including every finite residue level. -/

namespace ManuscriptAudit.EtaleProetaleCohomologyMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleProetaleInverseImage

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

private abbrev A := AddCommGrpCat.{u+1}
private abbrev C := Sheaf X.smallEtaleTopology A.{u}
private abbrev D := Sheaf (Scheme.ProEt.topology X) A.{u}

private theorem etaleGrothendieck : IsGrothendieckAbelian.{u+1} (C X) := by
  letI : EssentiallySmall.{u+1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology A.{u}

attribute [local instance] etaleGrothendieck

local instance etaleHasExt : HasExt.{u+1} (C X) := IsGrothendieckAbelian.hasExt (C X)

local instance inverseImageAdditive : (inverseImage X).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage X)

private abbrev integers := AddCommGrpCat.of (ULift.{u+1} ℤ)
private abbrev etaleIntegers := (constantSheaf X.smallEtaleTopology A.{u}).obj integers.{u}
private abbrev proetaleIntegers :=
  (constantSheaf (Scheme.ProEt.topology X) A.{u}).obj integers.{u}

private def integersIso : (inverseImage X).obj (etaleIntegers X) ≅ proetaleIntegers X :=
  (constantInverseImageIso X).app integers.{u}

/-- Cohomology of an actual étale coefficient maps to the cohomology of its inverse image. -/
def pullback (F : C X) (n : ℕ) : Sheaf.H F n →+ Sheaf.H ((inverseImage X).obj F) n :=
  ((Ext.mk₀ (integersIso X).inv).precomp ((inverseImage X).obj F) (zero_add n)).comp
    ((inverseImage X).mapExtAddHom (etaleIntegers X) F n)

theorem pullback_naturality {F G : C X} (f : F ⟶ G) (n : ℕ) (e : Sheaf.H F n) :
    pullback X G n (Sheaf.H.map f n e) =
      Sheaf.H.map ((inverseImage X).map f) n (pullback X F n e) := by
  change (Ext.mk₀ (integersIso X).inv).comp
      ((e.comp (Ext.mk₀ f) (add_zero n)).mapExactFunctor (inverseImage X)) (zero_add n) =
    ((Ext.mk₀ (integersIso X).inv).comp (e.mapExactFunctor (inverseImage X)) (zero_add n)).comp
      (Ext.mk₀ ((inverseImage X).map f)) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc]

/-- The direct-image comparison uses the counit of the actual adjunction in every degree. -/
def directImageComparison (F : D X) (n : ℕ) :
    Sheaf.H ((directImage X).obj F) n →+ Sheaf.H F n :=
  (Sheaf.H.map ((adjunction X).counit.app F) n).comp (pullback X ((directImage X).obj F) n)

/-- The native change of sites on constant-coefficient groups. -/
def constantComparison (M : A.{u}) (n : ℕ) :
    Sheaf.H ((constantSheaf X.smallEtaleTopology A.{u}).obj M) n →+
      Sheaf.H ((constantSheaf (Scheme.ProEt.topology X) A.{u}).obj M) n :=
  (Sheaf.H.map ((constantInverseImageIso X).app M).hom n).comp
    (pullback X ((constantSheaf X.smallEtaleTopology A.{u}).obj M) n)

theorem constantComparison_naturality {M N : A.{u}} (f : M ⟶ N) (n : ℕ)
    (e : Sheaf.H ((constantSheaf X.smallEtaleTopology A.{u}).obj M) n) :
    constantComparison X N n (Sheaf.H.map ((constantSheaf X.smallEtaleTopology A.{u}).map f) n e) =
      Sheaf.H.map ((constantSheaf (Scheme.ProEt.topology X) A.{u}).map f) n
        (constantComparison X M n e) := by
  simp only [constantComparison, AddMonoidHom.comp_apply, pullback_naturality]
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  have h := (constantInverseImageIso X).hom.naturality f
  exact congrArg (fun g => Sheaf.H.map g n (pullback X _ n e)) h

variable (Y : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev residueCoefficient (r : ℕ) :=
  AddCommGrpCat.uliftFunctor.{1}.obj (AddCommGrpCat.of (ZMod (ℓ^r)))

/-- Étale finite cyclic coefficients compare with the literal native pro-étale adic residues. -/
def nativeResidueComparison (r n : ℕ) :
    Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
      (residueCoefficient ℓ r)) n →+
    Sheaf.H ((ProetaleCoefficientUniverseLift.lift Y).obj
      (ProetaleResidueSheaves.residueSheaf Y ℓ r)) n :=
  (Sheaf.H.map (ProetaleDiscreteConstant.nativeResidueIso Y ℓ r).hom n).comp
    (constantComparison Y (residueCoefficient ℓ r) n)

end
end ManuscriptAudit.EtaleProetaleCohomologyMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleCohomologyMap.pullback,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.pullback_naturality,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.directImageComparison,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.constantComparison_naturality,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.nativeResidueComparison] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
