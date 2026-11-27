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
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc] <;> simp


theorem pullback_boundary {S : ShortComplex (C X)} (hS : S.ShortExact) (n : ℕ)
    (e : Sheaf.H S.X₃ n) :
    pullback X S.X₁ (n+1) (e.comp hS.extClass rfl) =
      (pullback X S.X₃ n e).comp (hS.map_of_exact (inverseImage X)).extClass rfl := by
  change (Ext.mk₀ (integersIso X).inv).comp
      ((e.comp hS.extClass rfl).mapExactFunctor (inverseImage X)) (zero_add (n+1)) =
    ((Ext.mk₀ (integersIso X).inv).comp (e.mapExactFunctor (inverseImage X)) (zero_add n)).comp
      (hS.map_of_exact (inverseImage X)).extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, Ext.comp_assoc] <;> simp

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
  simp only [constantComparison, AddMonoidHom.comp_apply]
  have hpb := pullback_naturality X ((constantSheaf X.smallEtaleTopology A.{u}).map f) n e
  refine (congrArg (fun c => Sheaf.H.map ((constantInverseImageIso X).app N).hom n c) hpb).trans ?_
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  have h : (inverseImage X).map ((constantSheaf X.smallEtaleTopology A.{u}).map f) ≫
      ((constantInverseImageIso X).app N).hom =
    ((constantInverseImageIso X).app M).hom ≫ (constantSheaf (Scheme.ProEt.topology X) A.{u}).map f :=
    (constantInverseImageIso X).hom.naturality f
  rw [h]

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

/-- The literal reduction in étale constant coefficients. -/
def etaleResidueTransition (r : ℕ) :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj (residueCoefficient ℓ (r+1)) ⟶
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj (residueCoefficient ℓ r) :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).map
    (AddCommGrpCat.uliftFunctor.{1}.map
      (AddCommGrpCat.ofHom (PadicResidueSystems.reduction ℓ (Nat.le_succ r)).toAddMonoidHom))

theorem nativeResidueComparison_transition (r n : ℕ) (e :
    Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
      (residueCoefficient ℓ (r+1))) n) :
    nativeResidueComparison Y ℓ r n (Sheaf.H.map (etaleResidueTransition Y ℓ r) n e) =
      Sheaf.H.map ((ProetaleCoefficientUniverseLift.lift Y).map
        (ProetaleResidueSheaves.residueTransition Y ℓ r)) n
        (nativeResidueComparison Y ℓ (r+1) n e) := by
  simp only [nativeResidueComparison, AddMonoidHom.comp_apply, etaleResidueTransition]
  let f : residueCoefficient ℓ (r+1) ⟶ residueCoefficient ℓ r :=
    AddCommGrpCat.uliftFunctor.{1}.map
      (AddCommGrpCat.ofHom (PadicResidueSystems.reduction ℓ (Nat.le_succ r)).toAddMonoidHom)
  have h := constantComparison_naturality Y f n e
  refine (congrArg (fun c => Sheaf.H.map (ProetaleDiscreteConstant.nativeResidueIso Y ℓ r).hom n c)
    h).trans ?_
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    ProetaleDiscreteConstant.nativeResidueIso_naturality]


end
end ManuscriptAudit.EtaleProetaleCohomologyMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleCohomologyMap.pullback,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.pullback_naturality,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.directImageComparison,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.pullback_boundary,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.constantComparison_naturality,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.nativeResidueComparison,
      ``ManuscriptAudit.EtaleProetaleCohomologyMap.nativeResidueComparison_transition] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
