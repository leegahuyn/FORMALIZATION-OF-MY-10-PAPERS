import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleDegreeOnePullback

/-! The actual degree-one small étale pullback is natural in each
coefficient sheaf and independent of its injective representative. -/

namespace ManuscriptAudit.OpenEtaleDegreeOneCoefficients

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtaleTwoOpenHOne EtaleHOneCokernelNaturality SheafH1Descent
open OpenEtaleExtension OpenEtaleHOneByRepresentatives OpenEtaleDegreeOnePullback

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
private abbrev A := AddCommGrpCat.{u}
private abbrev C := Sheaf X.smallEtaleTopology A.{u}
private abbrev R := restriction j A.{u}
private abbrev T (Z : Scheme.{u}) := identityObject Z
private abbrev t (Z : Scheme.{u}) := MorphismProperty.Over.mkIdTerminal @Etale Z

local instance : PreservesFiniteLimits (R j) := (restriction_exact j).1
local instance : PreservesFiniteColimits (R j) := (restriction_exact j).2
local instance : (R j).Additive := restriction_additive j

variable {F I G J : C (X := X)}
variable (m : F ⟶ I) (n : G ⟶ J) [Mono m] [Mono n]
variable (a : F ⟶ G) (b : I ⟶ J) (h : m ≫ b = a ≫ n)

private theorem square :
    (R j).map m ≫ (R j).map b = (R j).map a ≫ (R j).map n := by
  rw [← Functor.map_comp, h, Functor.map_comp]

private abbrev q := quotientMap m n a b h
private abbrev q' := quotientMap ((R j).map m) ((R j).map n)
  ((R j).map a) ((R j).map b) (square j m n a b h)

private theorem cokernelIso_map :
    (R j).map (q m n a b h) ≫ (PreservesCokernel.iso (R j) n).hom =
      (PreservesCokernel.iso (R j) m).hom ≫ q' j m n a b h := by
  let u := PreservesCokernel.iso (R j) m
  let v := PreservesCokernel.iso (R j) n
  let c := cokernel.π ((R j).map m) ≫ u.inv
  have hc : c = (R j).map (cokernel.π m) := by
    have hp := congrArg (· ≫ u.inv) (PreservesCokernel.π_iso_hom (R j) m).symm
    simpa only [c, Category.assoc, Iso.hom_inv_id, Category.comp_id] using hp
  letI : Epi c := inferInstanceAs (Epi (cokernel.π ((R j).map m) ≫ u.inv))
  apply (cancel_epi c).mp
  change c ≫ (R j).map (q m n a b h) ≫ v.hom = c ≫ u.hom ≫ q' j m n a b h
  have hp : cokernel.π m ≫ q m n a b h = b ≫ cokernel.π n := by simp [q, quotientMap]
  have hp' : cokernel.π ((R j).map m) ≫ q' j m n a b h =
      (R j).map b ≫ cokernel.π ((R j).map n) := by simp [q', quotientMap]
  calc
    c ≫ (R j).map (q m n a b h) ≫ v.hom =
        (R j).map (cokernel.π m ≫ q m n a b h) ≫ v.hom := by
      rw [hc, Functor.map_comp, Category.assoc]
    _ = (R j).map b ≫ cokernel.π ((R j).map n) := by
      rw [hp, Functor.map_comp, Category.assoc, PreservesCokernel.π_iso_hom]
    _ = c ≫ u.hom ≫ q' j m n a b h := by
      rw [← hp', c, Category.assoc, Iso.inv_hom_id_assoc]

private theorem cokernelSections_map (x : (cokernel m).obj.obj (op (T X))) :
    (q' j m n a b h).hom.app (op (T Y))
      (cokernelSectionEquiv j m ((cokernel m).obj.map (openArrow j).op x)) =
    cokernelSectionEquiv j n
      ((cokernel n).obj.map (openArrow j).op ((q m n a b h).hom.app (op (T X)) x)) := by
  let U := op (Scheme.Etale.mk j)
  let V := op (T Y)
  let u := PreservesCokernel.iso (R j) m
  let v := PreservesCokernel.iso (R j) n
  let g := q m n a b h
  let y := (cokernel m).obj.map (openArrow j).op x
  let z := sectionEquiv j (cokernel m) y
  have hsection : ((R j).map g).hom.app V z =
      sectionEquiv j (cokernel n) ((cokernel n).obj.map (openArrow j).op (g.hom.app (op (T X)) x)) := by
    calc
      _ = sectionEquiv j (cokernel n) (g.hom.app U y) :=
        (sectionEquiv_natural j g y).symm
      _ = _ := congrArg (sectionEquiv j (cokernel n))
        (NatTrans.naturality_apply g.hom (openArrow j).op x)
  have hm := congrArg (fun f : (R j).obj (cokernel m) ⟶ cokernel ((R j).map n) =>
    f.hom.app V z) (cokernelIso_map j m n a b h)
  change v.hom.hom.app V (((R j).map g).hom.app V z) =
    (q' j m n a b h).hom.app V (u.hom.hom.app V z) at hm
  exact hm.symm.trans (congrArg (v.hom.hom.app V) hsection)

variable [Injective I] [Injective J]

/-- The actual derived pullback in degree one commutes with the literal
map on coefficient cohomology. -/
theorem pullbackHOne_coeff (c : Sheaf.H F 1) :
    Sheaf.H.map ((R j).map a) 1 (pullbackHOne m j c) =
      pullbackHOne n j (Sheaf.H.map a 1 c) := by
  obtain ⟨x, rfl⟩ := connectingSection_surjective m (t X) c
  have h₁ := connectingSection_map m n a b h x
  have h₂ := pullbackHOne_connecting m j x
  have h₃ := pullbackHOne_connecting n j ((q m n a b h).hom.app (op (T X)) x)
  have h₄ := connectingSection_map ((R j).map m) ((R j).map n) ((R j).map a) ((R j).map b)
    (square j m n a b h) (cokernelSectionEquiv j m ((cokernel m).obj.map (openArrow j).op x))
  rw [h₁, h₂, h₃, h₄, cokernelSections_map]

/-- The pullback depends on the open immersion and coefficients alone. -/
theorem pullbackHOne_independent {F I J : C (X := X)} (m : F ⟶ I) (n : F ⟶ J)
    [Mono m] [Mono n] [Injective I] [Injective J] (c : Sheaf.H F 1) :
    pullbackHOne m j c = pullbackHOne n j c := by
  let b := Injective.factorThru n m
  have h : m ≫ b = 𝟙 F ≫ n := by
    rw [Category.id_comp]
    exact Injective.comp_factorThru n m
  simpa using pullbackHOne_coeff j m n (𝟙 F) b h c

/-- Canonical degree-one pullback on the actual small étale site. -/
noncomputable def pullback (F : C (X := X)) :
    Sheaf.H F 1 →+ Sheaf.H ((R j).obj F) 1 :=
  pullbackHOne (Injective.ι F) j

@[simp] theorem pullback_eq {F I : C (X := X)} (m : F ⟶ I) [Mono m] [Injective I]
    (c : Sheaf.H F 1) :
    pullback j F c = pullbackHOne m j c :=
  pullbackHOne_independent j (Injective.ι F) m c

end

end ManuscriptAudit.OpenEtaleDegreeOneCoefficients

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.OpenEtaleDegreeOneCoefficients.pullbackHOne_coeff,
      ``ManuscriptAudit.OpenEtaleDegreeOneCoefficients.pullbackHOne_independent,
      ``ManuscriptAudit.OpenEtaleDegreeOneCoefficients.pullback_eq] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
